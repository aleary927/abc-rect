#include "base/abc/abc.h" 
#include "misc/vec/vecInt.h"
#include "sat/bsat/satSolver.h"

ABC_NAMESPACE_IMPL_START

extern Abc_Ntk_t * Abc_NtkInter( Abc_Ntk_t * pNtkOn, Abc_Ntk_t * pNtkOff, int fRelation, int fVerbose );

Abc_Ntk_t * BuildCircuitWithTransforms(Abc_Ntk_t *pNtk);
Abc_Ntk_t * BuildTargetMiter(Abc_Ntk_t *pNtkSpec, Abc_Ntk_t *pNtkCircuit);
Abc_Obj_t * BuildOrTree(Abc_Ntk_t *pNtk, Vec_Ptr_t *vNodes);
Vec_Int_t * GetPiSatVarNums(Abc_Ntk_t *pNtk, int nIn, int startIdx);
void SubPiByIdx(Abc_Ntk_t *pNtk, int startIdx, Vec_Int_t *vConsts, int fDelete);

/*
Rectify a implementation by applying an iterative SAT-based approach. 
returns NULL if rectification not possible.
*/
Abc_Ntk_t * Abc_RectIterSat(Abc_Ntk_t *pNtkSpec, Abc_Ntk_t *pNtkImpl)
{
    /*
    important invariant: 
    All networks used in the iterative SAT loop will have the same number and ordering of PIs, even 
    if there exist unconnected PIs due to constant substitution.
    This enables the use of convenient built-in mitering functions.
    */
    int i, status;
    int nPiNum = Abc_NtkPiNum(pNtkSpec); // num primary inputs
    int iterations = 0; // K

    // convert circuit to transformed version (3 muxes and an AND gate)
    Abc_Ntk_t *pNtkCircuit = BuildCircuitWithTransforms(pNtkImpl); 
    int nTotalPi = Abc_NtkPiNum(pNtkCircuit); // all inputs
    int nXVarNum = nTotalPi - nPiNum; // transformation variables

    // Target = (Circuit(X, In) != Spec(In))
    Abc_Ntk_t *pNtkTarget = BuildTargetMiter(pNtkSpec, pNtkCircuit); 
    Abc_Ntk_t *pNtkTargetOrig = Abc_NtkDup(pNtkTarget);
    // TargetEq = (Circuit(X, In) == Spec(In))
    Abc_Ntk_t *pNtkTargetEq = Abc_NtkDup(pNtkTarget);       
    Abc_ObjXorFaninC(Abc_NtkPo(pNtkTargetEq, 0), 0); // Flip to "Equality"

    // network to accumulate all constraints
    // (Circuit(X, in_k) == Spec(in_k))
    Abc_Ntk_t *pNtkConstraintAcc = NULL; 

    while (1) 
    {
        iterations++;
        printf("Iteration %d \n", iterations);

        // convert aig into sat
        sat_solver *pSat = Abc_NtkMiterSatCreate(pNtkTarget, 0);
        status = sat_solver_solve(pSat, NULL, NULL, 0, 0, 0, 0);

        // IF UNSAT
        if (status == -1) {
            printf("No more counter-examples found. \n");
            sat_solver_delete(pSat);
            break; 
        }
        // error
        if (status != 1)
        {
            printf("Error during iterative SAT solving.\n");
            sat_solver_delete(pSat); 
            Abc_NtkDelete(pNtkTarget); 
            Abc_NtkDelete(pNtkTargetOrig);
            Abc_NtkDelete(pNtkTargetEq);
            if (pNtkConstraintAcc) 
            {
                Abc_NtkDelete(pNtkConstraintAcc);
            }
            return NULL;
        }

        // SAT
        // extract the input variable Counter-Example (in_k)
        Vec_Int_t *vInVars = GetPiSatVarNums(pNtkTarget, nPiNum, 0);
        int *in_k = Sat_SolverGetModel(pSat, vInVars->pArray, nPiNum);
        Vec_Int_t *vIn_k = Vec_IntAllocArray(in_k, nPiNum);
        sat_solver_delete(pSat);
        Vec_IntFree(vInVars);

        // create new constraint (Circuit(X, in_k) == Spec(in_k))
        Abc_Ntk_t *pNtkConstraint = Abc_NtkDup(pNtkTargetEq);
        // don't delete Pis after subsititution to keep consistent ordering
        SubPiByIdx(pNtkConstraint, 0, vIn_k, 0);
        
        // accumulate constraints 
        if (pNtkConstraintAcc == NULL) {
            pNtkConstraintAcc = pNtkConstraint;
        } else {
            Abc_Ntk_t *pNtkConstraintAccOld = pNtkConstraintAcc;
            pNtkConstraintAcc = Abc_NtkMiterAnd(pNtkConstraintAcc, pNtkConstraint, 0, 0);
            Abc_NtkDelete(pNtkConstraintAccOld);
            Abc_NtkDelete(pNtkConstraint);
        }

        // AND all accumulated constraints with original target miter
        pNtkTarget = Abc_NtkMiterAnd(pNtkTargetOrig, pNtkConstraintAcc, 0, 0);

        Vec_IntFree(vIn_k);
    }

    Abc_NtkDelete(pNtkTargetEq);

    // extract the final solution for X
    if (pNtkConstraintAcc == NULL) 
    {
        return NULL;
    }

    // solve for the final valid X assignment
    sat_solver * pSatFinal = Abc_NtkMiterSatCreate(pNtkConstraintAcc, 0);
    int statusFinal = sat_solver_solve(pSatFinal, NULL, NULL, 0, 0, 0, 0);

    if (statusFinal == 1) 
    {
        // Report stuff
        printf("\n=== RECTIFICATION REPORT ===\n");

        // get all X values for the muxes
        Vec_Int_t * vXVars = GetPiSatVarNums(pNtkConstraintAcc, nXVarNum, nPiNum);
        int * xVals = Sat_SolverGetModel(pSatFinal, vXVars->pArray, nXVarNum);
        Vec_Int_t *vXVals = Vec_IntAllocArray(xVals, nXVarNum);

        // Prints all nodes that were fixed
        Abc_Obj_t * pNode;
        int gateIdx = 0;
        int changeCount = 0;

        // compare the SAT result to the original Implementation nodes
        Abc_AigForEachAnd(pNtkImpl, pNode, i) 
        {
            int f0  = xVals[gateIdx * 3 + 0]; // invert f0
            int f1  = xVals[gateIdx * 3 + 1]; // invert f1
            int out = xVals[gateIdx * 3 + 2]; // invert out

            if (!f0 || !f1 || !out) 
            {
                changeCount++;
                printf("Node %d (Name: %s) fixed with config: [%d %d %d]\n", 
                        pNode->Id, Abc_ObjName(pNode), f0, f1, out);
            }
            gateIdx++;
        }
        printf("Total fix points identified: %d\n", changeCount);
        printf("============================\n\n");

        // apply transform values to circuit 
        SubPiByIdx(pNtkCircuit, nPiNum, vXVals, 1);
        Vec_IntFree(vXVars);
    } 
    else // cannot be rectified
    {
        printf("No valid transformation found.\n");
        Abc_NtkDelete(pNtkCircuit);
        pNtkCircuit = NULL;
    }

    // memory cleanup
    sat_solver_delete(pSatFinal);
    if (pNtkTarget) Abc_NtkDelete(pNtkTarget);
    if (pNtkConstraintAcc) Abc_NtkDelete(pNtkConstraintAcc);

    return pNtkCircuit;
}


/*
Rectify an implementation by iterating through nodes topographically, finding a node 
where rectification is possible, and computing a patch via interpolation.
Note: doesn't support multiple rectification points.
returns NULL if rectification not possible.
*/
Abc_Ntk_t * Abc_RectNaive(Abc_Ntk_t *pNtkSpec, Abc_Ntk_t *pNtkImpl)
{
    int i;
    Abc_Obj_t *pObj, *pTarget;
    int rectPossible = 0;
    Abc_Ntk_t *pNtkM0, *pNtkM1, *pNtkImplConstNode;
    Abc_Aig_t *pMan;

    Abc_AigForEachAnd(pNtkImpl, pObj, i)
    {
        pNtkImplConstNode = Abc_NtkDup(pNtkImpl);
        pMan = (Abc_Aig_t *) pNtkImplConstNode->pManFunc;
        Abc_AigReplace(pMan, pObj->pCopy, Abc_AigConst1(pNtkImplConstNode), 0);
        pNtkM1 = Abc_NtkMiter(pNtkSpec, pNtkImplConstNode, 0, 0, 0, 0);
        Abc_NtkDelete(pNtkImplConstNode);

        pNtkImplConstNode = Abc_NtkDup(pNtkImpl); 
        pMan = (Abc_Aig_t * ) pNtkImplConstNode->pManFunc;
        Abc_AigReplace(pMan, pObj->pCopy, Abc_ObjNot(Abc_AigConst1(pNtkImplConstNode)), 0);
        pNtkM0 = Abc_NtkMiter(pNtkSpec, pNtkImplConstNode, 0, 0, 0, 0);
        Abc_NtkDelete(pNtkImplConstNode);

        Abc_Ntk_t *pNtkAnd = Abc_NtkMiterAnd(pNtkM0, pNtkM1, 0, 0);
        if (Abc_NtkMiterSat(pNtkAnd, 0, 0, 0, NULL, NULL) == 1)
        {
            rectPossible = 1;
            pTarget = pObj;
            Abc_NtkDelete(pNtkAnd);
            break;
        }

        Abc_NtkDelete(pNtkAnd);
        Abc_NtkDelete(pNtkM0); 
        Abc_NtkDelete(pNtkM1);
    }

    if (!rectPossible)
    {
        printf("No rectification possible with single node change.\n");
        return NULL;
    }

    Abc_Ntk_t * pNtkPatch = Abc_NtkInter(pNtkM0, pNtkM1, 0, 0);

    if (pNtkPatch == NULL)
    {
        printf("Could not simplify patch using interpolation.\n");
        pNtkPatch = pNtkM0;
    }
    else 
    {
        Abc_NtkDelete(pNtkM0); 
    }
    Abc_NtkDelete(pNtkM1);

    Abc_Ntk_t* pNtkRect = Abc_NtkDup(pNtkImpl);

    // copy patch into rectified circuit
    Abc_NtkForEachPi(pNtkPatch, pObj, i)
    {
        pObj->pCopy = Abc_NtkPi(pNtkRect, i);
    }
    Abc_AigForEachAnd(pNtkPatch, pObj, i)
    {
        pObj->pCopy = Abc_AigAnd(
            (Abc_Aig_t *)pNtkRect->pManFunc, 
            Abc_ObjChild0Copy(pObj), 
            Abc_ObjChild1Copy(pObj)
        );
    }
    // replace targete node with patch
    Abc_AigReplace(
        (Abc_Aig_t *)pNtkRect->pManFunc, 
        pTarget->pCopy, 
        Abc_ObjChild0Copy(Abc_NtkPo(pNtkPatch, 0)), 
        0
    );

    Abc_NtkDelete(pNtkPatch);
    return pNtkRect;
}

/*
Replace all AND gates in the given network with AND gate that has a mux on each input and on output.
*/
Abc_Ntk_t * BuildCircuitWithTransforms(Abc_Ntk_t *pNtk)
{
    Abc_Ntk_t *pNtkCircuit = Abc_NtkDup(pNtk);
    Abc_Obj_t *pObj, *pNewPi, *pFanin0Mux, *pFanin1Mux, *pFaninMuxAnd;
    int i;
    Abc_AigForEachAnd(pNtk, pObj, i)
    {
        // build fanin MUXs
        pNewPi = Abc_NtkCreatePi(pNtkCircuit);
        pFanin0Mux = Abc_AigMux
            ((Abc_Aig_t *)pNtkCircuit->pManFunc, 
            pNewPi,     
            Abc_ObjChild0Copy(pObj), 
            Abc_ObjNot(Abc_ObjChild0Copy(pObj))
        );
        pNewPi = Abc_NtkCreatePi(pNtkCircuit);
        pFanin1Mux = Abc_AigMux(
            (Abc_Aig_t *)pNtkCircuit->pManFunc, 
            pNewPi, 
            Abc_ObjChild1Copy(pObj), 
            Abc_ObjNot(Abc_ObjChild1Copy(pObj))
        );
        // AND between fanin MUXs
        pFaninMuxAnd = Abc_AigAnd(
            (Abc_Aig_t *)pNtkCircuit->pManFunc, 
            pFanin0Mux, 
            pFanin1Mux
        );
        // output MUX
        pNewPi = Abc_NtkCreatePi(pNtkCircuit);
        Abc_Obj_t *pOutMux = Abc_AigMux(
            (Abc_Aig_t *)pNtkCircuit->pManFunc, 
            pNewPi, 
            pFaninMuxAnd, 
            Abc_ObjNot(pFaninMuxAnd)
        ); 
        // replace node
        Abc_AigReplace(
            (Abc_Aig_t *)pNtkCircuit->pManFunc, 
            pObj->pCopy,
            pOutMux,
            0
        );
        // new copy is now the output of the mux
        pObj->pCopy = pOutMux;
    }

    assert(Abc_AigCheck((Abc_Aig_t *)pNtkCircuit->pManFunc));
    assert(Abc_NtkPiNum(pNtkCircuit) == Abc_NtkPiNum(pNtk) + Abc_NtkNodeNum(pNtk)*3);
    return pNtkCircuit;
}

/*
Build a miter which is between specification network and a network which contains transformation variables in addition to 
the original PIs.
*/
Abc_Ntk_t * BuildTargetMiter(Abc_Ntk_t *pNtkSpec, Abc_Ntk_t *pNtkCircuit)
{
    int i;
    Abc_Ntk_t *pNtkTarget = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 0);

    // copy primary inputs from circuit to target
    Abc_Obj_t *pObj;
    Abc_NtkForEachPi(pNtkCircuit, pObj, i)
    {
        Abc_Obj_t *pNewPi = Abc_NtkCreatePi(pNtkTarget);
        pObj->pCopy = pNewPi;

        // set copy attribute for Pis in spec
        if (i < Abc_NtkPiNum(pNtkSpec))
        {
            Abc_NtkPi(pNtkSpec, i)->pCopy = pNewPi;
        }
    }

    // copy nodes from circuit to target 
    Abc_AigForEachAnd(pNtkCircuit, pObj, i)
    {
        Abc_Obj_t *pFanin0 = Abc_ObjChild0Copy(pObj);
        Abc_Obj_t *pFanin1 = Abc_ObjChild1Copy(pObj);
        pObj->pCopy = Abc_AigAnd((Abc_Aig_t *)pNtkTarget->pManFunc, pFanin0, pFanin1);
    }
    // copy nodes from spec to target 
    Abc_AigForEachAnd(pNtkSpec, pObj, i)
    {
        Abc_Obj_t *pFanin0 = Abc_ObjChild0Copy(pObj);
        Abc_Obj_t *pFanin1 = Abc_ObjChild1Copy(pObj);
        pObj->pCopy = Abc_AigAnd((Abc_Aig_t *)pNtkTarget->pManFunc, pFanin0, pFanin1);
    }

    Vec_Ptr_t *vXors = Vec_PtrAlloc(Abc_NtkPoNum(pNtkSpec));

    // create XORs for all outputs
    for (i = 0; i < Abc_NtkPoNum(pNtkSpec); i++)
    {
        Vec_PtrPush(
            vXors, 
            Abc_AigXor(
                (Abc_Aig_t *)pNtkTarget->pManFunc, 
                Abc_ObjChild0Copy(Abc_NtkPo(pNtkCircuit, i)), 
                Abc_ObjChild0Copy(Abc_NtkPo(pNtkSpec, i))
            )
        );
    }

    // create OR tree to join all XORs for miter output
    Abc_Obj_t *pMiterNode = BuildOrTree(pNtkTarget, vXors);
    Vec_PtrFree(vXors);

    // miter output for target
    Abc_Obj_t *pMiterPo = Abc_NtkCreatePo(pNtkTarget);
    Abc_ObjAddFanin(pMiterPo, pMiterNode);

    assert(Abc_AigCheck((Abc_Aig_t *)pNtkTarget->pManFunc));
    return pNtkTarget;
}

/*
Build a tree of ORs to join multiple nodes into a single node.
*/
Abc_Obj_t * BuildOrTree(Abc_Ntk_t *pNtk, Vec_Ptr_t *vNodes)
{
    // terminating conditions
    if (Vec_PtrSize(vNodes) == 0)
    {
        return Abc_ObjNot(Abc_AigConst1(pNtk));
    }
    if (Vec_PtrSize(vNodes) == 1)
    {
        return (Abc_Obj_t *)Vec_PtrEntry(vNodes, 0);
    }

    // create one level of ORs
    Vec_Ptr_t *vOutputs = Vec_PtrAlloc((Vec_PtrSize(vNodes) >> 1) + 1);
    for (int i = 0; i < Vec_PtrSize(vNodes); i += 2)
    {
        // handle case where odd number of nodes
        if (i == (Vec_PtrSize(vNodes) - 1))
        {
            Vec_PtrPush(vOutputs, Vec_PtrEntry(vNodes, i));
        }
        else 
        {
            Vec_PtrPush (
                vOutputs, 
                Abc_AigOr (
                    (Abc_Aig_t *)pNtk->pManFunc, 
                    (Abc_Obj_t *)Vec_PtrEntry(vNodes, i), 
                    (Abc_Obj_t *)Vec_PtrEntry(vNodes, i+1)
                )
            );
        }
    }

    // build next level
    Abc_Obj_t* retval = BuildOrTree(pNtk, vOutputs);
    Vec_PtrFree(vOutputs); 
    return retval;
}

/*
Get the SAT variable numbers for the PIs of the given network, assuming a miter was just created using the 
Abc_NtkMiterSatCreate function.
nIn: number of PIs vars to get 
startIdx: index of first PI var to get
*/
Vec_Int_t * GetPiSatVarNums(Abc_Ntk_t *pNtk, int nIn, int startIdx)
{
    Vec_Int_t * vCiIds;
    int i;
    vCiIds = Vec_IntAlloc( nIn );
    for (i = 0; i < nIn; i++)
    {
        Vec_IntPush( vCiIds, (int)(ABC_PTRINT_T)Abc_NtkPi(pNtk, i + startIdx)->pCopy );    
    }
    return vCiIds;
}

/*
Substitute PIs with constants in the vConsts vector starting with PI startIdx. 
If fDelete is true, also deletes the substituted PIs from the network. 
*/
void SubPiByIdx(Abc_Ntk_t *pNtk, int startIdx, Vec_Int_t *vConsts, int fDelete)
{
    Abc_Obj_t *pObj;
    int c, i;

    // substitution
    Vec_Ptr_t *vPis = Vec_PtrAlloc(vConsts->nSize);
    Vec_IntForEachEntry(vConsts, c, i)
    {
        pObj = Abc_NtkPi(pNtk, startIdx + i);
        Vec_PtrPush(vPis, pObj);
        if (c)
        {
            Abc_AigReplace((Abc_Aig_t *)pNtk->pManFunc, pObj, Abc_AigConst1(pNtk), 1);
        }
        else 
        {
            Abc_AigReplace((Abc_Aig_t *)pNtk->pManFunc, pObj, Abc_ObjNot(Abc_AigConst1(pNtk)), 1);
        }
    }

    if (!fDelete)
    {
        return;
    }

    // deletion
    Vec_PtrForEachEntry(Abc_Obj_t *, vPis, pObj, i)
    {
        assert(Abc_ObjFanoutNum(pObj) == 0);
        Abc_NtkDeleteObj(pObj);
    }

    Vec_PtrFree(vPis);
    assert(Abc_NtkCheck(pNtk));
}

ABC_NAMESPACE_IMPL_END