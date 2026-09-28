import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.SelectedHoleRegionRecognition
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonAlexanderConsequences
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall
import PoincareConjecture.Proofs.M76.Mathlib.ConvexPolyhedralNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSphereTopology
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import PoincareConjecture.Proofs.M76.Triangulation.PLDiskSurgeryModels

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem finitePLBallPair_of_compact_regularClosed_spherical_frontier
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E = 3) (hdimF : Module.finrank ℝ F = 3)
    {P : Set E} {D : Set F} (hP : IsCompact P) (hregular : closure (interior P) = P)
    (e : frontier P ≃ₜ frontier D) (he : e.IsFinitePL)
    (hD : IsCompact D) (hcv : Convex ℝ D) (hne : (interior D).Nonempty) :
    IsFinitePLBallPair P3 P (frontier P) := by
  obtain ⟨K, hK, hKcv, hPK⟩ := hP.exists_finite_convex_neighborhood
  have hfrontne : (frontier P).Nonempty :=
    (e.isConnected_of_convex_frontier hD hcv hne (by omega)).nonempty
  have hPne : P.Nonempty := hfrontne.mono hP.isClosed.frontier_subset
  have hKne : (interior K.space).Nonempty := hPne.mono hPK
  obtain ⟨U, hU, hUc, hUf, _, hball, hexterior⟩ := he.hasAlexanderRegionBalls
    hD hcv hne hdimF hdim (K.isCompact_space_of_finite hK) hKcv hKne
    (hP.isClosed.frontier_subset.trans hPK) K hK rfl
  have hPU : P ⊆ closure U := closed_subset_alexander_bounded_side hUf hexterior
    hP.isClosed Subset.rfl hPK
  have hUi : interior (closure U) = U := by
    rw [hball.interior_eq_sdiff_of_finrank_eq (by simp [Module.finrank_prod, hdim]),
      ← hUf, closure_sdiff_frontier, hU.interior_eq]
  have hPi : interior P ⊆ U := by
    rw [← hUi]
    exact interior_mono hPU
  have hPine : (interior P).Nonempty := by
    rw [← closure_nonempty_iff, hregular]
    exact hPne
  obtain ⟨x, hx⟩ := hPine
  have hdis : Disjoint (frontier (interior P)) U := by
    apply disjoint_left.mpr
    intro y hy hyU
    have hyf : y ∈ frontier U := hUf.symm.subset (frontier_interior_subset hy)
    exact hyf.2 (hU.interior_eq.symm ▸ hyU)
  have hUP := hUc.isPreconnected.m76_subset_of_disjoint_frontier isOpen_interior
    hdis ⟨x, hPi hx, hx⟩
  have hEq : P = closure U := Subset.antisymm hPU (by
    rw [← hregular]
    exact closure_mono hUP)
  rwa [← hEq] at hball

theorem finitePLBallPair_of_compact_plDomain_spherical_frontier
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E = 3) (hdimF : Module.finrank ℝ F = 3)
    {P : Set E} {D : Set F} {a : ι → OpenPartialHomeomorph E V3}
    (hP : IsCompact P) (ha : PLDomain a P)
    (e : frontier P ≃ₜ frontier D) (he : e.IsFinitePL)
    (hD : IsCompact D) (hcv : Convex ℝ D) (hne : (interior D).Nonempty) :
    IsFinitePLBallPair P3 P (frontier P) :=
  finitePLBallPair_of_compact_regularClosed_spherical_frontier hdim hdimF
    hP ha.closure_interior e he hD hcv hne

theorem finitePLBallPair_of_compact_plDomain_two_disk_frontier
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3)
    {P d k q : Set E} {a : ι → OpenPartialHomeomorph E V3}
    (hP : IsCompact P) (ha : PLDomain a P)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q) (hk : IsFinitePLBallPair (ℝ × ℝ) k q)
    (hdk : d ∩ k = q) (hfront : frontier P = d ∪ k) :
    IsFinitePLBallPair P3 P (d ∪ k) := by
  obtain ⟨e, he, _, _⟩ := hd.exists_sphere_model_of_disk_union hk hdk
  let f := (Homeomorph.setCongr hfront).trans e
  have hf : f.IsFinitePL := he.setCongr hfront.symm rfl
  have hhalf : Convex ℝ (TriangularRoofModel.halfBall 1) := by
    rw [TriangularRoofModel.halfBall_eq_halfspaces]
    simp only [ofPred_forall]
    exact convex_iInter fun i => (convex_Iic 0).affine_preimage
      (TriangularRoofModel.halfBallForms 1 i)
  have h := finitePLBallPair_of_compact_plDomain_spherical_frontier hdim
    (by simp [Module.finrank_prod]) hP ha f hf
    (TriangularRoofModel.isCompact_halfBall (Or.inl rfl)) hhalf
    (TriangularRoofModel.interior_halfBall_nonempty (Or.inl rfl))
  rwa [hfront] at h

end PoincareConjecture.M76
