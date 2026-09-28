import PoincareConjecture.Proofs.M25.Topology3D.Services

set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

theorem exists_nested_bridge_of_image_chain
    (A Gt Gp K0 F : D3) (S S0 MS MSp : Set E3) (CT CP CU : Fin 3 → Set E3)
    (hGt : Gt '' S = MS ∪ ⋃ k : Fin 3, CT k)
    (hGp : Gp '' (A '' S0) = MSp ∪ ⋃ k : Fin 3, CP k)
    (hK0M : K0 '' MSp = MS) (hK0cap : ∀ k : Fin 3, K0 '' CP k = CU k)
    (hF : F '' (MS ∪ ⋃ k : Fin 3, CU k) = MS ∪ ⋃ k : Fin 3, CT k) :
    ∃ Kmid : D3, Kmid '' S = S0 := by
  let Fp : D3 := (Gp.trans K0).trans F
  have hFp : Fp '' (A '' S0) = Gt '' S := by
    have h1 : Fp '' (A '' S0) = F '' (K0 '' (Gp '' (A '' S0))) := by
      simp only [Fp, Diffeomorph.coe_trans, Set.image_comp]
    rw [h1, hGp, Set.image_union, hK0M, Set.image_iUnion, hGt]
    simp only [hK0cap]
    exact hF
  refine ⟨(Gt.trans Fp.symm).trans A.symm, ?_⟩
  have h2 : ((Gt.trans Fp.symm).trans A.symm) '' S =
      A.symm '' (Fp.symm '' (Gt '' S)) := by
    simp only [Diffeomorph.coe_trans, Set.image_comp]
  rw [h2, ← hFp,
    Function.LeftInverse.image_image (fun x => Fp.symm_apply_apply x) (A '' S0),
    Function.LeftInverse.image_image (fun x => A.symm_apply_apply x) S0]

end PoincareConjecture.M25.Topology3D
