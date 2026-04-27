#include "base/abc/abc.h" 
#include "misc/vec/vecInt.h"
#include "sat/bsat/satSolver.h"

ABC_NAMESPACE_IMPL_START

Abc_Ntk_t * BuildCircuitWithTransforms(Abc_Ntk_t *pNtk);
Abc_Ntk_t * BuildTargetMiter(Abc_Ntk_t *pNtkSpec, Abc_Ntk_t *pNtkCircuit);
Abc_Obj_t * OrTree(Abc_Ntk_t *pNtk, Vec_Ptr_t *vNodes);

Vec_Int_t * GetPiSatVarNums(Abc_Ntk_t *pNtk, int nIn, int startIdx);
void SubPiByIdx(Abc_Ntk_t *pNtk, int startIdx, Vec_Int_t *vConsts, int fDelete);

Abc_Ntk_t * Abc_RectIterSat(Abc_Ntk_t *pNtkSpec, Abc_Ntk_t *pNtkImpl)
{
    int i, status;
    int nPiNum = Abc_NtkPiNum(pNtkSpec); // num primary inputs
    int iterations = 0; // K

    // convert circuit to transformed version (3 muxes and an AND gate)
    Abc_Ntk_t *pCircuit = BuildCircuitWithTransforms(pNtkImpl); 
    int nTotalPi = Abc_NtkPiNum(pCircuit); // all inputs
    int nXVarNum = nTotalPi - nPiNum; // transformation variables

    // build miter
    // Target = (Circuit(X, In) != Spec(In))
    Abc_Ntk_t *pTarget = BuildTargetMiter(pNtkSpec, pCircuit); 
    Abc_Ntk_t *pTargetOrig = Abc_NtkDup(pTarget);
    Abc_ObjXorFaninC(Abc_NtkPo(pTargetOrig, 0), 0); // Flip to "Equality"

    // store all constraints
    // (Circuit(X, in_k) == Spec(in_k))
    Abc_Ntk_t *pSuccessAcc = NULL; // TestSet

    while (true) 
    {
        iterations++;
        printf("Iteration %d \n", iterations);

        // convert aig into sat
        sat_solver *pSat = Abc_NtkMiterSatCreate(pTarget, 0);
        status = sat_solver_solve(pSat, NULL, NULL, 0, 0, 0, 0);

        // IF UNSAT
        if (status == -1) {
            printf("No more counter-examples found. \n");
            sat_solver_delete(pSat);
            break; 
        }

        // Otherwise Sat, then continue
        // extract the Counter-Example (in_k)
        Vec_Int_t *vInVars = GetPiSatVarNums(pTarget, nPiNum, 0);
        int *in_k = Sat_SolverGetModel(pSat, vInVars->pArray, nPiNum);
        Vec_Int_t *vIn_k = Vec_IntAllocArray(in_k, nPiNum);
        sat_solver_delete(pSat);
        Vec_IntFree(vInVars);

        // create constraint (Circuit(X, in_k) == Spec(in_k))
        Abc_Ntk_t *pConstraint = Abc_NtkDup(pTargetOrig);
        SubPiByIdx(pConstraint, 0, vIn_k, 0);
        
        // accumulate test patterns
        if (pSuccessAcc == NULL) {
            pSuccessAcc = pConstraint;
        } else {
            Abc_Ntk_t *pOldAcc = pSuccessAcc;
            pSuccessAcc = Abc_NtkMiterAnd(pSuccessAcc, pConstraint, 0, 0);
            Abc_NtkDelete(pOldAcc);
            Abc_NtkDelete(pConstraint);
        }

        // refine pTarget so no duplicate counterexamples found
        Abc_Ntk_t *pOldTarget = pTarget;
        pTarget = Abc_NtkMiterAnd(pTarget, pSuccessAcc, 0, 0);

        Abc_NtkDelete(pOldTarget);
        Vec_IntFree(vIn_k);
    }

    Abc_NtkDelete(pTargetOrig);

    // extract the final solution for X
    if (pSuccessAcc == NULL) return NULL;

    // solve for the final valid X assignment
    sat_solver * pSatFinal = Abc_NtkMiterSatCreate(pSuccessAcc, 0);
    int statusFinal = sat_solver_solve(pSatFinal, NULL, NULL, 0, 0, 0, 0);

    if (statusFinal == 1) 
    {
        // Report stuff
        printf("\n=== RECTIFICATION REPORT ===\n");

        // get all X values for the muxes
        Vec_Int_t * vXVars = GetPiSatVarNums(pSuccessAcc, nXVarNum, nPiNum);
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

            if (f0 || f1 || out) 
            {
                changeCount++;
                printf("Node %d (Name: %s) fixed with config: [%d %d %d]\n", 
                        pNode->Id, Abc_ObjName(pNode), f0, f1, out);
            }
            gateIdx++;
        }
        printf("Total fix points identified: %d\n", changeCount);
        printf("============================\n\n");

        // apply new values to rectified circuit 
        SubPiByIdx(pCircuit, nPiNum, vXVals, 1);
        Vec_IntFree(vXVars);
    } 
    else // cannot be rectified
    {
        printf("No valid transformation found.\n");
        Abc_NtkDelete(pCircuit);
        pCircuit = NULL;
    }

    // memory cleanup
    sat_solver_delete(pSatFinal);
    if (pTarget) Abc_NtkDelete(pTarget);
    if (pSuccessAcc) Abc_NtkDelete(pSuccessAcc);

    return pCircuit;
}


Abc_Ntk_t * Abc_RectNaive(Abc_Ntk_t *pNtkSpec, Abc_Ntk_t *pNtkImpl)
{
    int i;
    Abc_Obj_t *pNode;
    int rectPossible = 0;
    Abc_Print(-2, "Nodes: \n");
    Abc_Ntk_t *pNtkM0, *pNtkM1, *pNtkImplConstNode;
    Abc_Aig_t *pMan;
    Abc_AigForEachAnd(pNtkImpl, pNode, i)
    {

        printf("i: %d\n", i);
        pNtkImplConstNode = Abc_NtkDup(pNtkImpl);
        pMan = (Abc_Aig_t *) pNtkImplConstNode->pManFunc;
        Abc_AigReplace(pMan, pNode->pCopy, Abc_AigConst1(pNtkImplConstNode), 0);
        pNtkM1 = Abc_NtkMiter(pNtkSpec, pNtkImplConstNode, 0, 0, 0, 0);
        Abc_NtkDelete(pNtkImplConstNode);

        pNtkImplConstNode = Abc_NtkDup(pNtkImpl); 
        pMan = (Abc_Aig_t * ) pNtkImplConstNode->pManFunc;
        Abc_AigReplace(pMan, pNode->pCopy, Abc_ObjNot(Abc_AigConst1(pNtkImplConstNode)), 0);
        pNtkM0 = Abc_NtkMiter(pNtkSpec, pNtkImplConstNode, 0, 0, 0, 0);
        Abc_NtkDelete(pNtkImplConstNode);

        Abc_Ntk_t *pNtkAnd = Abc_NtkMiterAnd(pNtkM0, pNtkM1, 0, 0);
        if (Abc_NtkMiterSat(pNtkAnd, 0, 0, 0, NULL, NULL) == 1)
        {
            Abc_Print(-2, "Found node where rectification is possible.\n");
            rectPossible = 1;
            break;
        }

        Abc_NtkDelete(pNtkAnd);
        Abc_NtkDelete(pNtkM0);
        Abc_NtkDelete(pNtkM1);
    }

    // Abc_Obj_t *pTarget = pNode;

    // printf("Here\n");
    // Abc_AigForEachAnd(pNtkM0, pNode, i)
    // {
    //     pNode->pCopy = Abc_AigAnd((Abc_Aig_t *)pNtkImpl->pManFunc, Abc_ObjChild0Copy(pNode), Abc_ObjChild1Copy(pNode));
    // }
    // Abc_Obj_t *pRectNode = Abc_ObjFanin0(Abc_NtkCo(pNtkM0, 0));

    // Abc_AigReplace((Abc_Aig_t *)pNtkImpl->pManFunc, pTarget, pRectNode->pCopy, 0);

    // inter for patch
    // insert into impl network
    // replace target node with patch
    // Abc_AigReplace()

    // for each node:
        // check if rectification possible at node: 
        // create miter M0 (between spec and impl where target node is replaced by 0)
        // create miter M1 (between spec and impl where target node is replaced by 1) 
        // create network which is M0 AND M1 
        // if network UNSAT, rectification possible at target node, break loop

    // if rectification possible at some node:
    // compute interpolant
    // simplify interpolant 
    // insert interpolant into impl at target node

    Abc_Ntk_t* pNtkRect = NULL;
    return pNtkRect;
}

Abc_Ntk_t * BuildCircuitWithTransforms(Abc_Ntk_t *pNtk)
{
    Abc_Ntk_t *pNtkCircuit = Abc_NtkDup(pNtk);
    Abc_Obj_t *pObj, *pNewPi, *pFanin0Mux, *pFanin1Mux, *pFaninMuxAnd;
    int i;
    Abc_AigForEachAnd(pNtk, pObj, i)
    {
        // build fanin muxs
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

        // and between fanin muxs
        pFaninMuxAnd = Abc_AigAnd(
            (Abc_Aig_t *)pNtkCircuit->pManFunc, 
            pFanin0Mux, 
            pFanin1Mux
        );
        pNewPi = Abc_NtkCreatePi(pNtkCircuit);
        Abc_Obj_t *pOutMux = Abc_AigMux(
            (Abc_Aig_t *)pNtkCircuit->pManFunc, 
            pNewPi, 
            pFaninMuxAnd, 
            Abc_ObjNot(pFaninMuxAnd)
        ); 
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
    Abc_Obj_t *pMiterNode = OrTree(pNtkTarget, vXors);
    Vec_PtrFree(vXors);

    // miter output for target
    Abc_Obj_t *pMiterPo = Abc_NtkCreatePo(pNtkTarget);
    Abc_ObjAddFanin(pMiterPo, pMiterNode);

    assert(Abc_AigCheck((Abc_Aig_t *)pNtkTarget->pManFunc));

    return pNtkTarget;
}


Abc_Obj_t * OrTree(Abc_Ntk_t *pNtk, Vec_Ptr_t *vNodes)
{
    if (Vec_PtrSize(vNodes) == 0)
    {
        return Abc_ObjNot(Abc_AigConst1(pNtk));
    }
    if (Vec_PtrSize(vNodes) == 1)
    {
        return (Abc_Obj_t *)Vec_PtrEntry(vNodes, 0);
    }

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

    Abc_Obj_t* retval = OrTree(pNtk, vOutputs);
    Vec_PtrFree(vOutputs); 
    return retval;
}


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

void SubPiByIdx(Abc_Ntk_t *pNtk, int startIdx, Vec_Int_t *vConsts, int fDelete)
{
    Abc_Obj_t *pObj;
    int c, i;
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

    Vec_PtrForEachEntry(Abc_Obj_t *, vPis, pObj, i)
    {
        assert(Abc_ObjFanoutNum(pObj) == 0);
        Abc_NtkDeleteObj(pObj);
    }

    Vec_PtrFree(vPis);
    assert(Abc_NtkCheck(pNtk));
}

ABC_NAMESPACE_IMPL_END