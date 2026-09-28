import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Exterior
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.ContactGerms
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Regularization









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

private theorem halfInterval_component
    {M : Type*} [TopologicalSpace M] {K L : Set M}
    {γ : Real → M} {δ : Real} (hδ : 0 < δ)
    (hγ : ContinuousOn γ (Ioo (-δ) δ)) (hinj : InjOn γ (Ioo (-δ) δ))
    (hK : ∀ t ∈ Ioo (-δ) δ, γ t ∈ K ↔ 0 ≤ t)
    (hL : ∀ᶠ t in 𝓝 (0 : Real), γ t ∈ L) :
    (connectedComponentIn K (γ 0)).Nontrivial ∧
      ∃ z ∈ connectedComponentIn L (γ 0), z ∉ K := by
  obtain ⟨r, hr, hrL⟩ := Metric.eventually_nhds_iff.mp hL
  let s := min δ r / 2
  have hs : 0 < s := half_pos (lt_min hδ hr)
  have hsδ : s < δ := lt_of_lt_of_le (half_lt_self (lt_min hδ hr)) (min_le_left _ _)
  have hsr : s < r := lt_of_lt_of_le (half_lt_self (lt_min hδ hr)) (min_le_right _ _)
  have hsmall : Icc (-s) s ⊆ Ioo (-δ) δ := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hzero : (0 : Real) ∈ Ioo (-δ) δ := ⟨neg_neg_of_pos hδ, hδ⟩
  have hpos : γ '' Icc 0 s ⊆ connectedComponentIn K (γ 0) := by
    apply (isPreconnected_Icc.image γ (hγ.mono ?_)).subset_connectedComponentIn
      (mem_image_of_mem γ (left_mem_Icc.mpr hs.le))
    · rintro y ⟨t, ht, rfl⟩
      exact (hK t (hsmall ⟨by linarith [ht.1], ht.2⟩)).mpr ht.1
    · intro t ht
      exact hsmall ⟨by linarith [ht.1], ht.2⟩
  have hneg : γ '' Icc (-s) 0 ⊆ connectedComponentIn L (γ 0) := by
    apply (isPreconnected_Icc.image γ (hγ.mono ?_)).subset_connectedComponentIn
      (mem_image_of_mem γ (right_mem_Icc.mpr (neg_nonpos.mpr hs.le)))
    · rintro y ⟨t, ht, rfl⟩
      apply hrL
      rw [Real.dist_eq, sub_zero, abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · intro t ht
      exact hsmall ⟨ht.1, by linarith [ht.2]⟩
  refine ⟨⟨γ 0, hpos (mem_image_of_mem γ (left_mem_Icc.mpr hs.le)),
    γ s, hpos (mem_image_of_mem γ (right_mem_Icc.mpr hs.le)), ?_⟩,
    γ (-s), hneg (mem_image_of_mem γ (left_mem_Icc.mpr (by linarith))), ?_⟩
  · intro heq
    have := hinj hzero (hsmall ⟨by linarith, le_rfl⟩) heq
    linarith
  · intro hnegK
    have := (hK (-s) (hsmall ⟨le_rfl, by linarith⟩)).mp hnegK
    linarith



theorem exists_regular_completion_with_proper_components
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {p : S2} (hunique : ∀ q, h q = h p →
      mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, h (e x) = h p - x 0 ^ 2 + x 1 ^ 2)
    {r : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ e.source) :
    let K := connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r
    ∃ H : S2 → Real, ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ H ∧
      (∀ q, H q = h p → mfderiv (𝓡 2) 𝓘(Real, Real) H q ≠ 0) ∧
      (∀ q ∈ K, H =ᶠ[𝓝 q] h) ∧ K ⊆ H ⁻¹' {h p} ∧
      ∀ q ∈ K, (connectedComponentIn K q).Nontrivial ∧
        ∃ z ∈ connectedComponentIn (H ⁻¹' {h p}) q, z ∉ K := by
  let K := connectedComponentIn (h ⁻¹' {h p}) p \ e '' openSquare r
  have hball : closedBall (0 : E2) (r / 2) ⊆ openSquare r := by
    intro x hx
    have hn := mem_closedBall_zero_iff.mp hx
    exact ⟨lt_of_le_of_lt ((Real.norm_eq_abs (x 0)) ▸ PiLp.norm_apply_le x 0)
      (by linarith),
      lt_of_le_of_lt ((Real.norm_eq_abs (x 1)) ▸ PiLp.norm_apply_le x 1)
      (by linarith)⟩
  have hballsource := hball.trans ((openSquare_subset_closedSquare r).trans hrs)
  have hdis : Disjoint K (e '' closedBall (0 : E2) (r / 2)) := by
    apply disjoint_left.mpr
    intro q hq hqb
    exact hq.2 (image_mono hball hqb)
  have hform' (x : E2) (hx : x ∈ e.source) :
      h (e x) = h p + ∑ i : Fin 2, (![-1, 1] i : Real) * x i ^ 2 := by
    rw [hform x hx]
    simp [Fin.sum_univ_two]
    ring
  obtain ⟨H, hH, _, hreg, hgerm, hKL⟩ :=
    exists_compact_regular_completion_of_morse_exterior hh hunique e he0 hep he hei
      ![-1, 1] (by intro i; fin_cases i <;> norm_num) hform'
      (half_pos hr) hballsource
      (fun q hq => connectedComponentIn_subset _ _ hq.1) hdis
  obtain ⟨_, hboundary, _, _, hattach, _⟩ :=
    compact_regular_exterior hh hunique e he0 hep hform hr hrs
  refine ⟨H, hH, hreg, hgerm, hKL, ?_⟩
  intro q hq
  obtain ⟨i, hi⟩ := hattach q hq
  have hiK := connectedComponentIn_subset K q hi
  obtain ⟨δ, hδ, _, W, _, _, hγ, hinj, hlevel, _, _, hhalf⟩ :=
    exists_contact_halfInterval e he hei hr hrs hform i
  let γ : Real → S2 := fun t => e ((1 + t) • contact r i)
  have hγ0 : γ 0 = e (contact r i) := by simp [γ]
  have hzero : (0 : Real) ∈ Ioo (-δ) δ := ⟨neg_neg_of_pos hδ, hδ⟩
  have hcont : ContinuousAt γ 0 := hγ.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hzero)
  have hHL : ∀ᶠ t in 𝓝 (0 : Real), γ t ∈ H ⁻¹' {h p} := by
    have hevent := hcont.eventually (hγ0 ▸ hgerm _ hiK)
    filter_upwards [hevent, isOpen_Ioo.mem_nhds hzero] with t ht htδ
    change H (γ t) = h p
    rw [ht]
    exact (hlevel.symm ▸ mem_image_of_mem γ htδ).2
  have hhalf' : ∀ t ∈ Ioo (-δ) δ, γ t ∈ K ↔ 0 ≤ t := by
    simpa only [hep] using hhalf
  obtain ⟨hnontrivial, z, hz, hzK⟩ :=
    halfInterval_component hδ hγ.continuousOn hinj hhalf' hHL
  simp only [add_zero, one_smul] at hnontrivial hz
  rw [← connectedComponentIn_eq hi] at hnontrivial
  refine ⟨hnontrivial, z, ?_, hzK⟩
  have hiL := connectedComponentIn_mono q hKL hi
  rwa [← connectedComponentIn_eq hiL] at hz

end Poincare.Manifold.Schoenflies.SaddleLevel
