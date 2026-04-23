#include "base/abc/abc.h" 
#include "base/abc/abcInt.h"
#include "aig/gia/gia.h"
#include "base/main/main.h"
#include "misc/vec/vecInt.h"
#include "opt/fsim/fsimInt.h"
#include "opt/sim/sim.h"
#include "sat/bsat/satSolver.h"
#include "sat/cnf/cnf.h"

ABC_NAMESPACE_IMPL_START

extern Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );

Abc_Ntk_t * BuildCircuitWithTransforms(Abc_Ntk_t *pNtk);
Abc_Ntk_t * BuildTargetMiter(Abc_Ntk_t *pNtkSpec, Abc_Ntk_t *pNtkCircuit);
Abc_Obj_t * OrTree(Abc_Ntk_t *pNtk, Vec_Ptr_t *vNodes);

Abc_Ntk_t * BuildEqualityMiterWithFixedInput(Abc_Ntk_t * pSpec,Abc_Ntk_t * pCircuit, int * in_k, int nPi );
Vec_Int_t * GetSatVarNums(Abc_Ntk_t *pNtk, int nIn, int startIdx);

int * EvaluateNetwork(Abc_Ntk_t *pNtkSpec, int* pInputs);
void SubstituteConsts(Abc_Ntk_t *pNtk, int * pConsts, int nConsts, int startIdx);

void AndClause(Abc_Ntk_t *pNtkTarget, Abc_Ntk_t *pNtkClause);

Abc_Ntk_t * Abc_RectIterSat(Abc_Ntk_t *pNtkSpec, Abc_Ntk_t *pNtkImpl)
{
    // things I need to figure out how to do: 
    // 1. create miter between spec and circuit (circuit has extra PIs for transform variables)
    // 2. get SAT assignment for miter (both regular PIs and transform variables)
    // 3. keep track of PI assignments in the TestSet 
    // 4. 
    int i;

    int nPiNum = Abc_NtkPiNum(pNtkSpec);

    // replace each and gate with transform
    Abc_Ntk_t *pNtkCircuit = BuildCircuitWithTransforms(pNtkImpl);
    // build target miter
    Abc_Ntk_t *pNtkTarget = BuildTargetMiter(pNtkSpec, pNtkCircuit);


    // with xnor rather than xor 
    Abc_Ntk_t *pNtkTargetNot = Abc_NtkDup(pNtkTarget);
    Abc_Obj_t *pPo = Abc_NtkPo(pNtkTargetNot, 0);
    Abc_ObjXorFaninC(pPo, 0);
    
    Abc_AigCheck((Abc_Aig_t *)pNtkCircuit->pManFunc);
    Abc_AigCheck((Abc_Aig_t *)pNtkTarget->pManFunc);
    Abc_AigCheck((Abc_Aig_t *)pNtkTargetNot->pManFunc);

    // init TestSet
    Vec_Ptr_t *TestSet = Vec_PtrAlloc(Abc_NtkNodeNum(pNtkSpec) >> 1);   
    int k = 0;

    // iterative SAT loop
    while (1)
    {
        sat_solver * pSat = Abc_NtkMiterSatCreate(pNtkTarget, 0);

        // variable numbers corresponding to PIs of spec
        Vec_Int_t* vInIds = GetSatVarNums(pNtkTarget, nPiNum, 0);

        int status = sat_solver_solve(pSat, NULL, NULL, 0, 0, 0, 0);
        // error
        if (status == 0)
        {
            return NULL;
        }
        // UNSAT
        if (status == -1)
        {
            break;
        }
        // SAT
        if (status == 1)
        {
            k++;
            printf("k = %d\n", k);

            // in_k = sat assignment for input vars
            int * in_k = Sat_SolverGetModel(pSat, vInIds->pArray, nPiNum);

            // append in_k to TestSet
            Vec_PtrPush(TestSet, in_k);

            // add clauses/constraints
            Abc_Ntk_t * pNtkNewConstraints = Abc_NtkDup(pNtkTargetNot);
            Abc_AigCheck((Abc_Aig_t *)pNtkNewConstraints->pManFunc);
            SubstituteConsts(pNtkNewConstraints, in_k, nPiNum, 0);
            Abc_AigCheck((Abc_Aig_t *)pNtkNewConstraints->pManFunc);
            AndClause(pNtkTarget, pNtkNewConstraints);

            printf("node count: %d\n", Abc_NtkNodeNum(pNtkTarget));

            // Abc_Ntk_t * pNtkTargetOld = pNtkTarget; 
            // printf("fail here?\n");
            // pNtkTarget = Abc_NtkMiterAnd(pNtkTargetOld, pNtkNewConstraints, 0, 0);
            // Abc_NtkDelete(pNtkTargetOld);
            Abc_NtkDelete(pNtkNewConstraints);
        }
        // not possible?
        else
        {
            return NULL;
        }
    }
    printf("Done with loop after %d iterations.\n", k);
    Abc_NtkDelete(pNtkTarget);

    // build final formula and check if SAT
    Abc_Ntk_t* pNtkFinalFormula = Abc_NtkDup(pNtkTargetNot);
    SubstituteConsts(pNtkFinalFormula, Vec_PtrEntry(TestSet, 0), nPiNum, 0);
    for (i = 1; i < k; i++)
    {
        Abc_Ntk_t * pNtkFinalFormulaOld = pNtkFinalFormula;
        Abc_Ntk_t * pNtkNewClause = Abc_NtkDup(pNtkTargetNot);
        SubstituteConsts(pNtkNewClause, Vec_PtrEntry(TestSet, i), nPiNum, 0);
        pNtkFinalFormula = Abc_NtkMiterAnd(pNtkFinalFormula, pNtkNewClause, 0, 0);
        Abc_NtkDelete(pNtkFinalFormulaOld);
    }

    sat_solver * pSat = Abc_NtkMiterSatCreate(pNtkFinalFormula, 0);
    int status = sat_solver_solve(pSat, NULL, NULL, 0, 0, 0, 0);

    // if SAT: get transform variable assignment for solution and set X Pis of pNtkCircuit to consts
    // no solution
    if (status != 1)
    {
        // no solution
        return NULL;
    }

    printf("Solution found!\n");
    // extract parameter variable values 
    // find varNums for paramter variables 
    Vec_Int_t * vParamVarIds = GetSatVarNums(pNtkFinalFormula, 3*nPiNum, nPiNum);
    int * vals = Sat_SolverGetModel(pSat, vParamVarIds->pArray, 3*nPiNum);
    // substitute parameter variable values into pNtkCircuit
    SubstituteConsts(pNtkCircuit, vals, 3*nPiNum, nPiNum);

    Abc_NtkDelete(pNtkFinalFormula);
    Abc_NtkDelete(pNtkTargetNot);

    return pNtkCircuit;
}

Abc_Ntk_t * Abc_RectNaive(Abc_Ntk_t *pNtkSpec, Abc_Ntk_t *pNtkImpl)
{
    int i;
    Abc_Obj_t *pNode;
    int rectPossible = 0;
    Abc_Print(-2, "Nodes: \n");
    Abc_Ntk_t *pNtkM0, *pNtkM1, *pNtkImplConstNode;
    Abc_Aig_t *pMan;
    Abc_NtkForEachNode(pNtkImpl, pNode, i)
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

    Abc_Obj_t *pTarget = pNode;

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

    Abc_Ntk_t* pNtkRect;
    return pNtkRect;
}

// ============= NEW =====================
Abc_Ntk_t * Abc_RectCEGISClean(Abc_Ntk_t * pNtkSpec, Abc_Ntk_t * pNtkImpl) 
{
    int i;
    int nPiNum = Abc_NtkPiNum(pNtkSpec);

    // Build Circuits
    Abc_Ntk_t *pCircuit = BuildCircuitWithTransforms(pNtkImpl); // impl
    Abc_Ntk_t *pSpec = pNtkSpec;

    // Build Miter
    // Target = circuit(X, in) XOR spec(In)
    Abc_Ntk_t *pTarget = BuildTargetMiter(pSpec, pCircuit); 

    // initialize test set
    Vec_Ptr_t *vTestSet = Vec_PtrAlloc(100);

    int iterations = 0;

    // sat solver
    sat_solver *pSat;

    while (true) 
    {
        iterations++;
        printf("\n iterations: %d\n ", iterations);

        pSat = Abc_NtkMiterSatCreate(pTarget, 0);
        
        int status= sat_solver_solve(pSat, NULL, NULL, 0, 0, 0, 0);

        // if UNSAT
        if (status == -1) {
            printf("no counter example found, is UNSAT");
            sat_solver_delete(pSat);
            break;
        }

        if (status == 0) {
            printf("error");
            sat_solver_delete(pSat);
            return NULL;
        }

        // else is SAT

        // now get counter examples
        Vec_Int_t *vInVars = GetSatVarNums(pTarget, nPiNum, 0);

        int *in_k_raw = Sat_SolverGetModel(pSat, vInVars->pArray, nPiNum);

        Vec_PtrPush(vTestSet, in_k_raw);

        int * in_k = (int *)malloc(sizeof(int) * nPiNum);
        memcpy(in_k, in_k_raw, sizeof(int) * nPiNum);

        sat_solver_delete(pSat);

        printf("\n counter example found\n");

        // do circuit (x,In) == spec(in_k);

        Abc_Ntk_t *pFixedConstraint = BuildEqualityMiterWithFixedInput(pSpec, pCircuit, in_k, nPiNum);

        // refine -> targer = target ^ constraint
        Abc_Ntk_t *pOldTarget = pTarget;

        pTarget = Abc_NtkMiterAnd(pTarget, pFixedConstraint, 1, 1);

        Abc_NtkDelete(pOldTarget);
        Abc_NtkDelete(pFixedConstraint);
    }

    // solve for X only

    Abc_Ntk_t * pFinal = NULL;

    for (i = 0; i < Vec_PtrSize(vTestSet); i++) {
        int * in_k = (int *)Vec_PtrEntry(vTestSet, i);

        Abc_Ntk_t * pConstraint= BuildEqualityMiterWithFixedInput(pSpec, pCircuit, in_k, nPiNum);

        if (i == 0) {
            pFinal = pConstraint;
        }
        else {
            Abc_Ntk_t * pOld = pFinal;
            pFinal = Abc_NtkMiterAnd(pFinal, pConstraint, 1, 1);
            Abc_NtkDelete(pConstraint);
            Abc_NtkDelete(pOld);
        }
    }

    // solve for x

    sat_solver * pSatFinal = Abc_NtkMiterSatCreate(pFinal, 0);

    int status = sat_solver_solve(pSatFinal, NULL, NULL, 0, 0, 0, 0);
    
    if (status != 1)
    {
        printf("No valid transformation found\n");
        return NULL;
    }

    printf("Valid transformation found!\n");

    // Extract X 
    Vec_Int_t * vXVars = GetSatVarNums(pFinal, Abc_NtkPiNum(pFinal), nPiNum);
    int * xVals = Sat_SolverGetModel(pSatFinal, vXVars->pArray, Abc_NtkPiNum(pFinal) - nPiNum);

    // Apply Transforms

    SubstituteConsts(pCircuit, xVals, Abc_NtkPiNum(pFinal) - nPiNum, nPiNum);
    Abc_NtkDelete(pFinal);
    Abc_NtkDelete(pTarget);

    return pCircuit;
    
}

Abc_Ntk_t * BuildEqualityMiterWithFixedInput( Abc_Ntk_t * pSpec, Abc_Ntk_t * pCircuit, int * in_k, int nPi )
{
    int i;

    Abc_Ntk_t * pMiter = Abc_NtkAlloc(ABC_NTK_STRASH, ABC_FUNC_AIG, 1);

    // copy PIs
    Abc_Obj_t * pObj;
    Abc_NtkForEachPi(pCircuit, pObj, i)
    {
        Abc_Obj_t * pNewPi = Abc_NtkCreatePi(pMiter);
        pObj->pCopy = pNewPi;

        if (i < nPi)
            Abc_NtkPi(pSpec, i)->pCopy = pNewPi;
    }

    // build circuit logic
    Abc_AigForEachAnd(pCircuit, pObj, i)
    {
        pObj->pCopy =
            Abc_AigAnd((Abc_Aig_t *)pMiter->pManFunc,
                       Abc_ObjChild0Copy(pObj),
                       Abc_ObjChild1Copy(pObj));
    }

    // build spec logic
    Abc_AigForEachAnd(pSpec, pObj, i)
    {
        pObj->pCopy =
            Abc_AigAnd((Abc_Aig_t *)pMiter->pManFunc,
                       Abc_ObjChild0Copy(pObj),
                       Abc_ObjChild1Copy(pObj));
    }

    // XOR outputs (equality check)
    Vec_Ptr_t * vXor = Vec_PtrAlloc(Abc_NtkPoNum(pSpec));

    for (i = 0; i < Abc_NtkPoNum(pSpec); i++)
    {
        Vec_PtrPush(vXor,
            Abc_AigXor((Abc_Aig_t *)pMiter->pManFunc,
                       Abc_ObjChild0Copy(Abc_NtkPo(pCircuit, i)),
                       Abc_ObjChild0Copy(Abc_NtkPo(pSpec, i))));
    }

    Abc_Obj_t * pOr = OrTree(pMiter, vXor);
    Vec_PtrFree(vXor);

    Abc_Obj_t * pPo = Abc_NtkCreatePo(pMiter);
    Abc_ObjAddFanin(pPo, pOr);

    // IMPORTANT: apply constant inputs
    SubstituteConsts(pMiter, in_k, nPi, 0);

    return pMiter;
}
// ============= NEW =====================


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
        Abc_Obj_t *pOutMux = Abc_AigMux(
            (Abc_Aig_t *)pNtkCircuit->pManFunc, 
            pNewPi, 
            pFaninMuxAnd, 
            Abc_ObjNot(pFaninMuxAnd)
        ); 
        pNewPi = Abc_NtkCreatePi(pNtkCircuit);
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


Vec_Int_t * GetSatVarNums(Abc_Ntk_t *pNtk, int nIn, int startIdx)
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

int * EvaluateNetwork(Abc_Ntk_t *pNtkSpec, int * pInputs)
{
    Aig_Man_t * pAig = Abc_NtkToDar(pNtkSpec, 0, 0);
    // create sat solver
    Cnf_Dat_t * pCnf = Cnf_Derive(pAig, 1);

    sat_solver *pSat = sat_solver_new();
    Cnf_DataWriteIntoSolver(pCnf, 1, 0);

    Abc_Obj_t *pObj; 
    int i;
    Abc_NtkForEachPi(pNtkSpec, pObj, i)
    {
        int v = pCnf->pVarNums[pObj->Id];
        lit l = toLitCond(v, pInputs[i] ? 0 : 1);
        sat_solver_addclause(pSat, &l, &l + 1);
    }

    int pPoVarNums[Abc_NtkPoNum(pNtkSpec)];
    Abc_NtkForEachPo(pNtkSpec, pObj, i)
    {
        pPoVarNums[i] = pCnf->pVarNums[pObj->Id];
    }

    int status = sat_solver_solve(pSat, NULL, NULL, 0, 0, 0, 0);
    printf("status: %d\n", status);

    return Sat_SolverGetModel(pSat, pPoVarNums, Abc_NtkPoNum(pNtkSpec));
}


void SubstituteConsts(Abc_Ntk_t *pNtk, int * pConsts, int nConsts, int startIdx)
{
    Abc_Obj_t *pObj;
    int i;
    int nPiNumStart = Abc_NtkPiNum(pNtk);
    for (i = 0; i < nConsts; i++)
    {
        pObj = Abc_NtkPi(pNtk, i + startIdx);

        if (pConsts[i])
        {
            Abc_AigReplace((Abc_Aig_t *)pNtk->pManFunc, pObj, Abc_AigConst1(pNtk), 1);
        }
        else 
        {
            Abc_AigReplace((Abc_Aig_t *)pNtk->pManFunc, pObj, Abc_ObjNot(Abc_AigConst1(pNtk)), 1);
        }
        // Abc_NtkDeleteObj(pObj);
    }
    // assert(nPiNumStart - nConsts == Abc_NtkPiNum(pNtk));
    Gia_Obj_t *pAnd; 
    Gia_ParSim_t *pPars; 
    Gia_ManSim_t *pManSim; 
    Gia_Man_t *pAig; 
    assert(Abc_AigCheck((Abc_Aig_t *)pNtk->pManFunc));
}

void AndClause(Abc_Ntk_t *pNtkTarget, Abc_Ntk_t *pNtkClause)
{
    int tVarIdx = Abc_NtkPiNum(pNtkTarget) - Abc_NtkPiNum(pNtkClause);

    int i; 
    Abc_Obj_t *pObj;

    Abc_NtkForEachPi(pNtkClause, pObj, i)
    {
        pObj->pCopy = Abc_NtkPi(pNtkTarget, i + tVarIdx);
    }

    // copy clause structure into target
    Abc_AigForEachAnd(pNtkClause, pObj, i)
    {
        Abc_Obj_t *pFanin0 = Abc_ObjChild0Copy(pObj);
        Abc_Obj_t *pFanin1 = Abc_ObjChild1Copy(pObj);
        pObj->pCopy = Abc_AigAnd((Abc_Aig_t *)pNtkTarget->pManFunc, pFanin0, pFanin1);
    }

    // create and between clause output and current target output
    Abc_Obj_t *pClauseOut = Abc_ObjChild0Copy(Abc_NtkPo(pNtkClause, 0));
    Abc_Obj_t *pTargetOut = Abc_ObjChild0(Abc_NtkPo(pNtkTarget, 0));
    Abc_Obj_t *pAnd = Abc_AigAnd((Abc_Aig_t *)pNtkTarget->pManFunc, pTargetOut, pClauseOut);

    // replace target output with and
    Abc_ObjPatchFanin(Abc_NtkPo(pNtkTarget, 0), Abc_ObjIsComplement(pTargetOut) ? Abc_ObjNot(pTargetOut) : pTargetOut, pAnd);

    assert(Abc_AigCheck((Abc_Aig_t *)pNtkTarget->pManFunc));
}

ABC_NAMESPACE_IMPL_END