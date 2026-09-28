import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.Regular
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Intervals.Contacts

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.SaddleLevel
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1
local notation "IR2" => 𝓘(Real, Real × Real)

private theorem exists_rectangle_around_closed_interval
    {a b : Real} (hab : a ≤ b) {W : Set (Real × Real)} (hW : IsOpen W)
    (hI : Icc a b ×ˢ {(0 : Real)} ⊆ W) :
    ∃ η δ : Real, 0 < η ∧ 0 < δ ∧
      Ioo (a - η) (b + η) ×ˢ Ioo (-δ) δ ⊆ W := by
  obtain ⟨U, V, hU, hV, hIU, h0V, hUV⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hW hI
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hIU ⟨le_rfl, hab⟩))
  obtain ⟨σ, hσ, hσU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hIU ⟨hab, le_rfl⟩))
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0V rfl))
  let η := min ρ σ / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηρ : η < ρ := by dsimp [η]; linarith [min_le_left ρ σ]
  have hησ : η < σ := by dsimp [η]; linarith [min_le_right ρ σ]
  refine ⟨η, δ, hη, hδ, ?_⟩
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  apply hUV
  constructor
  · by_cases hsa : s < a
    · apply hρU
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.1]
    · by_cases hbs : b < s
      · apply hσU
        rw [mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hs.2]
      · exact hIU ⟨le_of_not_gt hsa, le_of_not_gt hbs⟩
  · apply hδV
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using ht

theorem exists_physical_height_interval_strip
    {H h : S2 -> Real} (hH : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ H)
    (c : Real) (hreg : ∀ q, H q = c -> mfderiv (𝓡 2) 𝓘(Real, Real) H q ≠ 0)
    (p : S2) (hp : H p = c) (γ : Real -> S2)
    (hγ : ContMDiff 𝓘(Real, Real) (𝓡 2) ∞ γ) (hγinj : Function.Injective γ)
    (hγder : ∀ t, Function.Injective (mfderiv 𝓘(Real, Real) (𝓡 2) γ t))
    (hγC : range γ ⊆ connectedComponentIn (H ⁻¹' {c}) p)
    {a b : Real} (hab : a ≤ b) (hgerm : ∀ s ∈ Icc a b, H =ᶠ[𝓝 (γ s)] h) :
    ∃ (η δ : Real) (e : OpenPartialHomeomorph (Real × Real) S2),
      0 < η ∧ 0 < δ ∧ e.source = Ioo (a - η) (b + η) ×ˢ Ioo (-δ) δ ∧
      ContMDiffOn IR2 (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) IR2 ∞ e.symm e.target ∧
      (∀ s, e (s, 0) = γ s) ∧ ∀ z ∈ e.source, h (e z) = c + z.2 := by
  obtain ⟨ε, hε, F, hFs, hF, hFi, hcentral, hheight⟩ :=
    exists_regular_level_interval_strip hH c hreg p hp γ hγ hγinj hγder hγC
  let W : Set (Real × Real) := F.source ∩ F ⁻¹' interior {q : S2 | H q = h q}
  have hW : IsOpen W := hF.continuousOn.isOpen_inter_preimage F.open_source isOpen_interior
  have hIW : Icc a b ×ˢ {(0 : Real)} ⊆ W := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    have ht0 : t = 0 := ht
    subst t
    constructor
    · rw [hFs]
      exact ⟨mem_univ _, by constructor <;> linarith⟩
    · change F (s, 0) ∈ interior {q : S2 | H q = h q}
      rw [hcentral]
      exact mem_interior_iff_mem_nhds.mpr (hgerm s hs)
  obtain ⟨η, δ, hη, hδ, hrect⟩ := exists_rectangle_around_closed_interval hab hW hIW
  let B : Set (Real × Real) := Ioo (a - η) (b + η) ×ˢ Ioo (-δ) δ
  have hB : IsOpen B := isOpen_Ioo.prod isOpen_Ioo
  let e := F.restrOpen B hB
  have hes : e.source = B := by
    rw [F.restrOpen_source B hB]
    exact inter_eq_right.mpr (fun z hz => (hrect hz).1)
  refine ⟨η, δ, e, hη, hδ, hes, hF.mono inter_subset_left,
    hFi.mono inter_subset_left, hcentral, ?_⟩
  intro z hz
  have hzB : z ∈ B := hes ▸ hz
  have hzW := hrect hzB
  have heq : H (F z) = h (F z) :=
    interior_subset (s := {q : S2 | H q = h q}) hzW.2
  change h (F z) = c + z.2
  rw [← heq]
  exact hheight z.1 z.2 ((hFs ▸ hzW.1).2)

theorem exists_actual_exterior_interval_strips
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p ->
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 -> q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2)
    {r : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ e.source) :
    let K := connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r
    ∀ q ∈ K, ∃ (γ : Real -> S2) (a b η δ : Real)
        (F : OpenPartialHomeomorph (Real × Real) S2),
      ContMDiff 𝓘(Real, Real) (𝓡 2) ∞ γ ∧ Topology.IsEmbedding γ ∧
      (∀ t, Function.Injective (mfderiv 𝓘(Real, Real) (𝓡 2) γ t)) ∧
      a < b ∧ γ '' Icc a b = connectedComponentIn K q ∧
      range (fun i : Fin 2 × Fin 2 => e (contact r i)) ∩ connectedComponentIn K q =
        {γ a, γ b} ∧ 0 < η ∧ 0 < δ ∧
      F.source = Ioo (a - η) (b + η) ×ˢ Ioo (-δ) δ ∧
      ContMDiffOn IR2 (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) IR2 ∞ F.symm F.target ∧
      (∀ s, F (s, 0) = γ s) ∧ ∀ z ∈ F.source, h (F z) = h p + z.2 := by
  let K := connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r
  obtain ⟨H, hH, hreg, hgerm, hKL, hintervals⟩ :=
    exists_exterior_interval_parametrizations hh hunique e he0 hep he hei hform hr hrs
  obtain ⟨_, hlocal, hcontacts⟩ :=
    exterior_completion_boundary hh hunique e he0 hep he hei hform hr hrs H hgerm
  dsimp only
  intro q hq
  obtain ⟨γ, a, b, z, hγ, hγe, hγder, hab, hγI, hz, hγrange⟩ := hintervals q hq
  have hends : range (fun i : Fin 2 × Fin 2 => e (contact r i)) ∩ connectedComponentIn K q =
      {γ a, γ b} := by
    apply Poincare.Topology.inter_connectedComponentIn_eq_interval_endpoints
      hKL hz hγe hab hγI hγrange hlocal
    intro x hx
    obtain ⟨δ, α, hδ, hα, hα0, _, hαL, hαK⟩ := hcontacts x hx
    exact ⟨δ, hδ, α, hα, hα0, hαL, hαK⟩
  have hγC : range γ ⊆ connectedComponentIn (H ⁻¹' {h p}) q :=
    hγrange ▸ sdiff_subset
  have hγgerm (s : Real) (hs : s ∈ Icc a b) : H =ᶠ[𝓝 (γ s)] h := by
    apply hgerm
    apply connectedComponentIn_subset K q
    rw [← hγI]
    exact mem_image_of_mem γ hs
  obtain ⟨η, δ, F, hη, hδ, hFs, hF, hFi, hcentral, hheight⟩ :=
    exists_physical_height_interval_strip hH (h p) hreg q (hKL hq) γ hγ hγe.injective
      hγder hγC hab.le hγgerm
  exact ⟨γ, a, b, η, δ, F, hγ, hγe, hγder, hab, hγI, hends, hη, hδ,
    hFs, hF, hFi, hcentral, hheight⟩

end Poincare.Manifold.Schoenflies.SaddleLevel

end

end M38Schoenflies
