import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Coordinates

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

private theorem contact_abs {r : Real} (hr : 0 < r) (i : Fin 2 × Fin 2) (j : Fin 2) :
    |contact r i j| = r := by
  rcases i with ⟨i, k⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> simp [contact, abs_of_pos hr]

private theorem contact_ne_zero {r : Real} (hr : 0 < r)
    (i : Fin 2 × Fin 2) (j : Fin 2) : contact r i j ≠ 0 := by
  intro heq
  have hh := contact_abs hr i j
  rw [heq, abs_zero] at hh
  linarith

private theorem zeroLevel_collinear_contact {r : Real} (hr : 0 < r)
    (i : Fin 2 × Fin 2) {x : E2} (hx : x 0 ^ 2 = x 1 ^ 2)
    (hpos : 0 < x 0 / contact r i 0) (hside : 0 < contact r i 1 * x 1) :
    x = (x 0 / contact r i 0) • contact r i := by
  have h0 : (x 0 / contact r i 0) * contact r i 0 = x 0 :=
    div_mul_cancel₀ _ (contact_ne_zero hr i 0)
  have hs := (contact_mem hr i).2
  have hsq : x 1 ^ 2 = ((x 0 / contact r i 0) * contact r i 1) ^ 2 := by
    rw [mul_pow, ← hs, ← mul_pow, h0, hx]
  have h1 : x 1 = (x 0 / contact r i 0) * contact r i 1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hgood | hbad
    · exact hgood
    · have hstrict := mul_pos hpos (sq_pos_of_ne_zero (contact_ne_zero hr i 1))
      nlinarith
  ext j
  fin_cases j
  · exact h0.symm
  · exact h1

private theorem scaled_contact_mem_openSquare_iff {r t : Real} (hr : 0 < r)
    (i : Fin 2 × Fin 2) (ht : 0 < 1 + t) :
    (1 + t) • contact r i ∈ openSquare r ↔ t < 0 := by
  change |(1 + t) * contact r i 0| < r ∧
    |(1 + t) * contact r i 1| < r ↔ t < 0
  rw [abs_mul, abs_mul, abs_of_pos ht, contact_abs hr i 0, contact_abs hr i 1]
  constructor
  · intro hx
    nlinarith [hx.1]
  · intro ht0
    constructor <;> nlinarith

theorem exists_contact_halfInterval
    {h : S2 → Real} (e : OpenPartialHomeomorph E2 S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    {r c : Real} (hr : 0 < r) (hrs : closedSquare r ⊆ e.source)
    (hform : ∀ x ∈ e.source, h (e x) = c - x 0 ^ 2 + x 1 ^ 2)
    (i : Fin 2 × Fin 2) :
    ∃ δ : Real, 0 < δ ∧ δ < 1 ∧
      ∃ W : Set S2, IsOpen W ∧ e (contact r i) ∈ W ∧
        let γ : Real → S2 := fun t => e ((1 + t) • contact r i)
        ContMDiffOn 𝓘(Real, Real) (𝓡 2) ∞ γ (Ioo (-δ) δ) ∧
        InjOn γ (Ioo (-δ) δ) ∧
        W ∩ h ⁻¹' {c} = γ '' Ioo (-δ) δ ∧
        (∀ t ∈ Ioo (-δ) δ,
          e.symm (γ t) 0 / contact r i 0 - 1 = t) ∧
        ContMDiffOn (𝓡 2) 𝓘(Real, Real) ∞
          (fun q => e.symm q 0 / contact r i 0 - 1) W ∧
        (∀ t ∈ Ioo (-δ) δ,
          γ t ∈ connectedComponentIn (h ⁻¹' {c}) (e 0) \ e '' openSquare r ↔ 0 ≤ t) := by
  let z := contact r i
  let φ : Real → E2 := fun t => (1 + t) • z
  have hφ : ContDiff Real ∞ φ := (contDiff_const.add contDiff_id).smul contDiff_const
  have hz : z ∈ e.source := hrs (contact_mem hr i).1.1
  have hzero : (0 : Real) ∈ φ ⁻¹' e.source := by simpa [φ] using hz
  obtain ⟨R, hR, hRs⟩ := Metric.mem_nhds_iff.mp
    ((e.open_source.preimage hφ.continuous).mem_nhds hzero)
  let δ := min (R / 2) (1 / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hφs : MapsTo φ (Ioo (-δ) δ) e.source := by
    intro t ht
    apply hRs
    rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_lt]
    have hδR : δ < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    constructor <;> linarith [ht.1, ht.2]
  have htpos : ∀ t ∈ Ioo (-δ) δ, 0 < 1 + t := fun t ht => by linarith [ht.1]
  let A : Set E2 := {x | x 0 / z 0 - 1 ∈ Ioo (-δ) δ ∧ 0 < z 1 * x 1}
  have hA : IsOpen A :=
    (isOpen_Ioo.preimage (((EuclideanSpace.proj 0).continuous.div_const (z 0)).sub
      continuous_const)).inter
      (isOpen_lt continuous_const (continuous_const.mul (EuclideanSpace.proj 1).continuous))
  let W := e.target ∩ e.symm ⁻¹' A
  have hW : IsOpen W := e.isOpen_inter_preimage_symm hA
  have hφratio (t : Real) : φ t 0 / z 0 - 1 = t := by
    change (1 + t) * z 0 / z 0 - 1 = t
    rw [mul_div_cancel_right₀ _ (contact_ne_zero hr i 0)]
    ring
  have hφside (t : Real) (ht : 0 < 1 + t) : 0 < z 1 * φ t 1 := by
    change 0 < z 1 * ((1 + t) * z 1)
    nlinarith [mul_pos ht (sq_pos_of_ne_zero (contact_ne_zero hr i 1))]
  have hφlevel (t : Real) (ht : t ∈ Ioo (-δ) δ) : h (e (φ t)) = c := by
    rw [hform _ (hφs ht)]
    have hs := (contact_mem hr i).2
    change c - ((1 + t) * z 0) ^ 2 + ((1 + t) * z 1) ^ 2 = c
    change z 0 ^ 2 = z 1 ^ 2 at hs
    rw [mul_pow, mul_pow, hs]
    ring
  have himage : W ∩ h ⁻¹' {c} = (fun t => e (φ t)) '' Ioo (-δ) δ := by
    ext q
    constructor
    · rintro ⟨⟨hqt, hqA⟩, hqc⟩
      let t := e.symm q 0 / z 0 - 1
      have ht : t ∈ Ioo (-δ) δ := hqA.1
      have hs : (e.symm q) 0 ^ 2 = (e.symm q) 1 ^ 2 := by
        have hf := hform (e.symm q) (e.map_target hqt)
        rw [e.right_inv hqt] at hf
        change h q = c at hqc
        linarith
      have hcol := zeroLevel_collinear_contact hr i hs
        (show 0 < e.symm q 0 / z 0 by dsimp [t] at ht; linarith [ht.1]) hqA.2
      have heq : φ t = e.symm q := by
        rw [hcol]
        dsimp [φ, t]
        congr 1
        ring
      refine ⟨t, ht, ?_⟩
      change e (φ t) = q
      rw [heq, e.right_inv hqt]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨e.map_source (hφs ht), ?_⟩, hφlevel t ht⟩
      change e.symm (e (φ t)) ∈ A
      rw [e.left_inv (hφs ht)]
      exact ⟨by rwa [hφratio], hφside t (htpos t ht)⟩
  have hγ : ContMDiffOn 𝓘(Real, Real) (𝓡 2) ∞ (fun t => e (φ t)) (Ioo (-δ) δ) :=
    he.comp hφ.contMDiff.contMDiffOn hφs
  have hcontactC : e z ∈ connectedComponentIn (h ⁻¹' {c}) (e 0) :=
    square_zeroLevel_subset_component e hr hrs hform
      ⟨z, ⟨(contact_mem hr i).1.1, (contact_mem hr i).2⟩, rfl⟩
  have hγC : (fun t => e (φ t)) '' Ioo (-δ) δ ⊆
      connectedComponentIn (h ⁻¹' {c}) (e 0) := by
    have hconn := isPreconnected_Ioo.image (fun t => e (φ t)) hγ.continuousOn
    have hsub : (fun t => e (φ t)) '' Ioo (-δ) δ ⊆
        connectedComponentIn (h ⁻¹' {c}) (e z) := hconn.subset_connectedComponentIn
      (show e z ∈ (fun t => e (φ t)) '' Ioo (-δ) δ from
        ⟨0, ⟨neg_neg_of_pos hδ, hδ⟩, by simp [φ]⟩)
      (by rintro q ⟨t, ht, rfl⟩; exact hφlevel t ht)
    rwa [← connectedComponentIn_eq hcontactC] at hsub
  refine ⟨δ, hδ, hδ1, W, hW, ?_, hγ, ?_, himage, ?_, ?_, ?_⟩
  · have : e (φ 0) ∈ W := ((himage.symm ▸
      (show e (φ 0) ∈ (fun t => e (φ t)) '' Ioo (-δ) δ from
        ⟨0, ⟨neg_neg_of_pos hδ, hδ⟩, rfl⟩)) : e (φ 0) ∈ W ∩ h ⁻¹' {c}).1
    simpa [φ] using this
  · intro t ht u hu htu
    have heq := e.injOn (hφs ht) (hφs hu) htu
    have hh := congrArg (fun x : E2 => x 0 / z 0 - 1) heq
    simpa only [hφratio] using hh
  · intro t ht
    rw [e.left_inv (hφs ht)]
    exact hφratio t
  · exact (((EuclideanSpace.proj 0).contDiff.div_const (z 0)).sub
      contDiff_const).contMDiff.comp_contMDiffOn (hei.mono inter_subset_left)
  · intro t ht
    have hC := hγC ⟨t, ht, rfl⟩
    have himage : e (φ t) ∈ e '' openSquare r ↔ φ t ∈ openSquare r := by
      constructor
      · rintro ⟨x, hx, heq⟩
        exact e.injOn (hrs (openSquare_subset_closedSquare r hx)) (hφs ht) heq ▸ hx
      · exact mem_image_of_mem e
    change e (φ t) ∈ connectedComponentIn (h ⁻¹' {c}) (e 0) ∧
      e (φ t) ∉ e '' openSquare r ↔ 0 ≤ t
    rw [and_iff_right hC, himage, scaled_contact_mem_openSquare_iff hr i (htpos t ht)]
    exact not_lt

end Poincare.Manifold.Schoenflies.SaddleLevel
