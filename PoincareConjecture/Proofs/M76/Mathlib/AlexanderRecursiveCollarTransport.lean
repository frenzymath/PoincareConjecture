import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCollarSlab
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveFiberRestriction
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveFixedSlabs
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineLevelComplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections











set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem AlexanderCollarSlab.nonempty_of_slab_eq {S S' : Set E}
    {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ} (M : AlexanderCollarSlab S A q β)
    (hslab : S ∩ {x | A x ∈ Icc 0 β} = S' ∩ {x | A x ∈ Icc 0 β}) :
    Nonempty (AlexanderCollarSlab S' A q β) := by
  have hbase : S ∩ {x | A x = 0} = S' ∩ {x | A x = 0} := by
    have hzero (x : E) (hx : A x = 0) : A x ∈ Icc 0 β := by
      rw [hx]
      exact ⟨le_rfl, M.width_pos.le⟩
    ext x
    exact ⟨fun hx => ⟨(hslab.subset ⟨hx.1, hzero x hx.2⟩).1, hx.2⟩,
      fun hx => ⟨(hslab.symm.subset ⟨hx.1, hzero x hx.2⟩).1, hx.2⟩⟩
  have hdomain : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (M.upper p.1)} =
      {p : E × ℝ | p.1 ∈ S' ∩ {x | A x = 0} ∧ p.2 ∈ Icc 0 (M.upper p.1)} := by
    rw [hbase]
  let C := (Homeomorph.setCongr hdomain.symm).trans
    (M.chart.trans (Homeomorph.setCongr rfl))
  exact ⟨{
    width_pos := M.width_pos
    apex_mem := (hbase.subset ⟨M.apex_mem, M.apex_height⟩).1
    apex_height := M.apex_height
    upper := M.upper
    collar := M.collar
    residual := M.residual
    residualComplex := M.residualComplex
    chart := C
    chart_finitePL := M.chart_finitePL.setCongr hdomain rfl
    residual_finite := M.residual_finite
    residual_space := M.residual_space
    cover := M.cover.trans hslab
    residual_zero := M.residual_zero
    roof_contact := fun p => M.roof_contact ⟨p, hdomain.symm ▸ p.property⟩
    upper_finitePL := hbase ▸ M.upper_finitePL
    upper_bounds := fun x hx => M.upper_bounds x (hbase.symm ▸ hx)
    apex_upper := M.apex_upper
    upper_pos := fun x hx => M.upper_pos x (hbase.symm ▸ hx)
    height := fun p => M.height ⟨p, hdomain.symm ▸ p.property⟩
    bottom := fun p => M.bottom ⟨p, hdomain.symm ▸ p.property⟩
    bottom_covered := hbase.symm.subset.trans M.bottom_covered }⟩

variable [FiniteDimensional ℝ E]





theorem AlexanderCollarSlab.nonempty_cut_restriction {S s₀ s₁ : Set E}
    {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ} (M : AlexanderCollarSlab S A q β)
    (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁) (hunion : s₀ ∪ s₁ = S)
    (hdisj : (S ∩ {x | A x ∈ Icc 0 β}) ∩ (s₀ ∩ s₁) = ∅)
    (hq : q ∈ s₀) (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hKs : K.space = s₀) :
    Nonempty (AlexanderCollarSlab s₀ A q β) := by
  have hsS : s₀ ⊆ S := subset_union_left.trans hunion.subset
  have hT : M.collar ⊆ S ∩ {x | A x ∈ Icc 0 β} :=
    subset_union_left.trans M.cover.subset
  have hcut : M.collar ∩ (s₀ ∩ s₁) = ∅ :=
    eq_empty_iff_forall_notMem.mpr (fun _ hx =>
      (hdisj.subset ⟨hT hx.1, hx.2⟩).elim)
  have hcover : M.collar ⊆ s₀ ∪ s₁ :=
    (hT.trans inter_subset_left).trans hunion.symm.subset
  have hfiber := M.chart.collar_fiber_mem_cut_iff_of_disjoint M.bottom hs₀ hs₁ hcover hcut
  let B : Set (E × ℝ) := {p | p.1 ∈ s₀ ∩ {x | A x = 0} ∧
    p.2 ∈ Icc 0 (M.upper p.1)}
  have hB : B ⊆ {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (M.upper p.1)} := fun _ hx =>
    ⟨⟨hsS hx.1.1, hx.1.2⟩, hx.2⟩
  have htest (p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (M.upper p.1)}) :
      (p : E × ℝ) ∈ B ↔ (M.chart p : E) ∈ M.collar ∩ s₀ := by
    constructor
    · exact fun hp => ⟨(M.chart p).property, (hfiber p).1.mpr hp.1.1⟩
    · exact fun hp => ⟨⟨(hfiber p).1.mp hp.2, p.property.1.2⟩, p.property.2⟩
  have hCcopy := M.chart_finitePL.symm
  obtain ⟨_, ⟨L, hL, hLT, _⟩, _⟩ := hCcopy
  obtain ⟨W, hW, hWs⟩ := L.exists_finite_triangulation_inter K hL hK
  have hWT : W.space = M.collar ∩ s₀ := by rw [hWs, hLT, hKs]
  let C := M.chart.restrictSubsets hB inter_subset_left htest
  have hC : C.IsFinitePL := M.chart_finitePL.restrictSubsets_of_target
    hB inter_subset_left htest W hW hWT
  obtain ⟨J, hJ, hJs⟩ := M.residualComplex.exists_finite_triangulation_inter K
    M.residual_finite hK
  have hJR : J.space = M.residual ∩ s₀ := by rw [hJs, M.residual_space, hKs]
  obtain ⟨Z, hZ, hZs⟩ := K.exists_finite_affineLevel_complex hK A 0
  rw [hKs] at hZs
  have hZB : Z.space ⊆ S ∩ {x | A x = 0} :=
    hZs.subset.trans (inter_subset_inter_left _ hsS)
  have hupper : FinitePiecewiseAffineOn M.upper (s₀ ∩ {x | A x = 0}) :=
    hZs ▸ M.upper_finitePL.restrict Z hZ hZB
  refine ⟨{
    width_pos := M.width_pos
    apex_mem := hq
    apex_height := M.apex_height
    upper := M.upper
    collar := M.collar ∩ s₀
    residual := M.residual ∩ s₀
    residualComplex := J
    chart := C
    chart_finitePL := hC
    residual_finite := hJ
    residual_space := hJR
    cover := ?_
    residual_zero := fun _ hx => M.residual_zero ⟨hx.1.1, hx.2⟩
    roof_contact := ?_
    upper_finitePL := hupper
    upper_bounds := fun x hx => M.upper_bounds x ⟨hsS hx.1, hx.2⟩
    apex_upper := M.apex_upper
    upper_pos := fun x hx => M.upper_pos x ⟨hsS hx.1, hx.2⟩
    height := fun p => M.height ⟨p, hB p.property⟩
    bottom := fun p => M.bottom ⟨p, hB p.property⟩
    bottom_covered := fun _ hx => ⟨M.bottom_covered ⟨hsS hx.1, hx.2⟩, hx.1⟩ }⟩
  · calc
      (M.collar ∩ s₀) ∪ (M.residual ∩ s₀) = (M.collar ∪ M.residual) ∩ s₀ := by
        ext x
        simp only [mem_inter_iff, mem_union]
        tauto
      _ = s₀ ∩ {x | A x ∈ Icc 0 β} := by
        rw [M.cover]
        ext x
        exact ⟨fun hx => ⟨hx.2, hx.1.2⟩, fun hx => ⟨⟨hsS hx.1, hx.2⟩, hx.1⟩⟩
  · intro p
    constructor
    · exact fun hp => (M.roof_contact ⟨p, hB p.property⟩).mp hp.1
    · exact fun hp => ⟨(M.roof_contact ⟨p, hB p.property⟩).mpr hp, (C p).property.2⟩




theorem AlexanderCollarSlab.nonempty_supported_capped_cut
    {S s₀ s₁ d : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁) (hunion : s₀ ∪ s₁ = S)
    (hq : q ∈ s₀) (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hKs : K.space = s₀)
    (L : E → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hcut : s₀ ∩ s₁ ⊆ {x | L x = 0}) (hd : d ⊆ {x | L x = 0})
    (hband : ∀ x : E, A x ∈ Icc 0 β → δ ≤ |L x|)
    (H : E ≃ₜ E) (hfix : ∀ x, δ ≤ |L x| → H x = x) :
    (H '' (s₀ ∪ d)) ∩ {x | A x ∈ Icc 0 β} = s₀ ∩ {x | A x ∈ Icc 0 β} ∧
      Nonempty (AlexanderCollarSlab (H '' (s₀ ∪ d)) A q β) := by
  have hnonzero (x : E) (hx : A x ∈ Icc 0 β) : L x ≠ 0 := by
    intro hz
    have h := hband x hx
    rw [hz, abs_zero] at h
    exact (not_le_of_gt hδ) h
  have hdisj : (S ∩ {x | A x ∈ Icc 0 β}) ∩ (s₀ ∩ s₁) = ∅ :=
    eq_empty_iff_forall_notMem.mpr (fun x hx => hnonzero x hx.1.2 (hcut hx.2))
  obtain ⟨M₀⟩ := M.nonempty_cut_restriction hs₀ hs₁ hunion hdisj hq K hK hKs
  have hdV : Disjoint d {x | A x ∈ Icc 0 β} :=
    disjoint_left.mpr (fun x hxd hx => hnonzero x hx (hd hxd))
  have heq := H.capped_image_inter_eq_of_fixedOn
    (s := s₀) (fun x hx => hfix x (hband x hx)) hdV
  exact ⟨heq, M₀.nonempty_of_slab_eq heq.symm⟩

end Geometry
