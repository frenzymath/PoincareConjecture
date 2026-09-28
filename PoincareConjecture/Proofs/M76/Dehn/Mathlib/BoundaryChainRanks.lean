import PoincareConjecture.Proofs.M76.Dehn.Mathlib.BoundaryChainIntersection
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K A : SimplicialComplex ℝ E) [Fintype K.vertices] [Fintype A.vertices]

local notation "KA" => K.vertexAbstractComplex.toPreAbstractSimplicialComplex
local notation "AA" => A.vertexAbstractComplex.toPreAbstractSimplicialComplex

open Classical in

theorem boundary_topCycle_rank_bound (hAK : A ≤ K)
    (hcofaces : ∀ t : Triangle KA, (tetrahedronCofaces KA t).card =
      if t.val.map (Function.Embedding.subtype _) ∈ A.faces then 1 else 2)
    (hconn : (tetrahedronGraph KA).Connected)
    (hboundaryCofaces : ∀ e : Edge AA, (triangleCofaces AA e).card = 2)
    (t : Triangle AA) :
    Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary AA).dualMap) +
        Nat.card (Tetrahedron KA) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary KA).dualMap) + 1 := by
  classical
  let B : Triangle KA → Prop := fun q =>
    q.val.map (Function.Embedding.subtype _) ∈ A.faces
  let W := K.subcomplexTopCycles A hAK
  let T := LinearMap.range (triangleCoboundary KA).dualMap
  let Z := LinearMap.ker (edgeCoboundary KA).dualMap
  have hW : Module.finrank (ZMod 2) W =
      Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary AA).dualMap) :=
    (Submodule.equivMapOfInjective
      (LinearMap.funLeft (ZMod 2) (ZMod 2) (K.subcomplexFaceEmbedding A hAK 3)).dualMap
      (dual_restrict_injective _) (LinearMap.ker (edgeCoboundary AA).dualMap)).finrank_eq.symm
  have ht : B (K.subcomplexFaceEmbedding A hAK 3 t) := by
    change (K.subcomplexFaceEmbedding A hAK 3 t).val.map
      (Function.Embedding.subtype _) ∈ A.faces
    rw [K.subcomplexFaceEmbedding_forget]
    exact t.property.1
  have hinj := boundary3_injective_of_boundary_nonempty KA B hcofaces hconn
    ⟨K.subcomplexFaceEmbedding A hAK 3 t, ht⟩
  have hT : Module.finrank (ZMod 2) T = Nat.card (Tetrahedron KA) := by
    have h := LinearMap.finrank_range_of_inj hinj
    rw [Subspace.dual_finrank_eq, Module.finrank_pi] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hInf : Module.finrank (ZMod 2) (W ⊓ T : Submodule (ZMod 2) _) = 1 := by
    change Module.finrank (ZMod 2)
      (K.subcomplexTopCycles A hAK ⊓ LinearMap.range (triangleCoboundary KA).dualMap :
        Submodule (ZMod 2) (Module.Dual (ZMod 2) (Triangle KA → ZMod 2))) = 1
    rw [K.subcomplexTopCycles_inf_tetrahedron_boundaries A hAK hcofaces hconn hboundaryCofaces]
    exact finrank_span_singleton (K.subcomplex_markedTriangleChain_ne_zero A hAK t)
  have hWZ : W ≤ Z := K.subcomplexTopCycles_le_ker A hAK
  have hTZ : T ≤ Z := by
    rintro z ⟨c, rfl⟩
    exact boundary2_boundary3 KA c
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq W T
  have hle := Submodule.finrank_mono (sup_le hWZ hTZ)
  rw [hInf, hW, hT] at hdim
  dsimp only [Z] at hle
  omega

end Geometry.SimplicialComplex
