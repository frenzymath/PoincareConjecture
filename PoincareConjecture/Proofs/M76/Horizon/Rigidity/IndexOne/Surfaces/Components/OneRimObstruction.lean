import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.OneBoundaryCount
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.EssentialRims
import Mathlib.Analysis.Convex.Contractible



set_option autoImplicit false
open Set Metric Geometry BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

open Classical in
theorem false_of_single_generating_essential_rim
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hconn : IsPathConnected K.space) (hLK : L ≤ K)
    (gamma : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ L.space) (hgamma : gamma.IsFinitePL)
    (hboundary : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if s ∈ L.faces then 1 else 2)
    (delta : AddCircle (4 * (128 : ℝ)) ≃ₜ L.space)
    (hbij : Function.Bijective (FundamentalGroup.map
      ((ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le hLK)).comp
        (delta : C(AddCircle (4 * (128 : ℝ)), L.space))) 0))
    (hlocal : ∀ x : L.space,
      ∃ c : OpenPartialHomeomorph (L.space × Ico (0 : ℝ) 1) K.space,
        collarBase x ∈ c.source ∧ ∀ a, collarBase a ∈ c.source →
          c (collarBase a) = Set.inclusion (SimplicialComplex.space_subset_of_le hLK) a) :
    False := by
  let inclusion := ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le hLK)
  have hgen : Function.Surjective (FundamentalGroup.map inclusion (delta 0)) := by
    intro z
    obtain ⟨a, ha⟩ := hbij.2 z
    refine ⟨FundamentalGroup.map (delta : C(AddCircle (4 * (128 : ℝ)), L.space)) 0 a, ?_⟩
    rw [FundamentalGroup.map_comp, MonoidHom.comp_apply] at ha
    exact ha
  obtain ⟨_, Q, _, hcv, hne, H, _, _⟩ := isFinitePLBallPair_of_generating_boundary
    K L hK hpure hlinks hconn hLK gamma hgamma hboundary (delta 0) hgen hlocal
  let : ContractibleSpace Q := hcv.contractibleSpace (hne.mono interior_subset)
  let : ContractibleSpace K.space := H.contractibleSpace
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  let : Nontrivial (FundamentalGroup (AddCircle (4 * (128 : ℝ))) 0) :=
    AddCircle.nontrivial_fundamentalGroup_zero _
  let : Nontrivial (FundamentalGroup K.space (inclusion (delta 0))) := hbij.1.nontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (FundamentalGroup K.space (inclusion (delta 0)))
  exact hab (Subsingleton.elim _ _)

end PoincareConjecture.M76.HamiltonIntervalTorus
