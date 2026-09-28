import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckThinEnd
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckFrontierLevel
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckGraphSideAlignment












noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28




theorem exists_frontier_neck_sphere_sides_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (_D : LeviCivitaData g)
        (N N' : EpsilonNeck g),
        N.epsilon = N'.epsilon → N.epsilon ≤ epsilon₀ →
        ∀ (γ : ℝ → M) (s c : ℝ), s < c →
          ContinuousOn γ (Icc s c) → γ s = N.center → γ c = N'.center →
          MapsTo γ (Ico s c) N.carrier → N'.center ∈ frontier N.carrier →
          ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
            ∃ v ∈ Ioo s c,
              sigma * (N.coordinate_inverse (γ v)).2 = 509 * N.epsilon⁻¹ / 512 ∧
              (∀ t ∈ Ioo v c, 509 * N.epsilon⁻¹ / 512 <
                sigma * (N.coordinate_inverse (γ t)).2) ∧
              N'.center ∈ closure (neckSignedRegion N sigma
                (127 * N.epsilon⁻¹ / 128) N.epsilon⁻¹) ∧
              N'.center ∈ closure (neckSignedRegion N sigma
                (255 * N.epsilon⁻¹ / 256) N.epsilon⁻¹) ∧
              neckSignedRegion N sigma (127 * N.epsilon⁻¹ / 128) N.epsilon⁻¹ ⊆
                N'.region (-(N'.epsilon⁻¹ / 2)) (N'.epsilon⁻¹ / 2) ∧
              ∃ phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
                (∀ p, phi p = (N'.coordinate_inverse
                  (N.coordinate_map (p, sigma * (255 * N.epsilon⁻¹ / 256)))).1) ∧
                ∃ f : UnitTwoSphere → ℝ,
                  ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f ∧
                  (∀ p, |f p| < 7 * N'.epsilon⁻¹ / 8) ∧
                  (∀ p, N.coordinate_map (phi.symm p, sigma * (255 * N.epsilon⁻¹ / 256)) =
                    N'.coordinate_map (p, f p)) ∧
                  range (fun p : UnitTwoSphere =>
                    N.coordinate_map (p, sigma * (255 * N.epsilon⁻¹ / 256))) =
                    range (fun p : UnitTwoSphere => N'.coordinate_map (p, f p)) ∧
                  SmoothSphereIsotopicIn N.carrier
                    (range (fun p : UnitTwoSphere =>
                      N.coordinate_map (p, sigma * (255 * N.epsilon⁻¹ / 256))))
                    N.central_sphere ∧
                  SmoothSphereIsotopicIn N'.carrier
                    (range (fun p : UnitTwoSphere =>
                      N.coordinate_map (p, sigma * (255 * N.epsilon⁻¹ / 256))))
                    N'.central_sphere ∧
                  ContinuousOn (neckGraphHeight N' f) N'.carrier ∧
                  (∀ x ∈ N'.carrier, neckGraphHeight N' f x = 0 ↔
                    x ∈ range (fun p : UnitTwoSphere =>
                      N.coordinate_map (p, sigma * (255 * N.epsilon⁻¹ / 256)))) ∧
                  IsOpen (N'.carrier ∩ neckGraphHeight N' f ⁻¹' Iio 0) ∧
                  IsOpen (N'.carrier ∩ neckGraphHeight N' f ⁻¹' Ioi 0) ∧
                  Disjoint (N'.carrier ∩ neckGraphHeight N' f ⁻¹' Iio 0)
                    (N'.carrier ∩ neckGraphHeight N' f ⁻¹' Ioi 0) ∧
                  (N'.carrier ∩ neckGraphHeight N' f ⁻¹' Iio 0) ∪
                      (N'.carrier ∩ neckGraphHeight N' f ⁻¹' Ioi 0) =
                    N'.carrier \ range (fun p : UnitTwoSphere =>
                      N.coordinate_map (p, sigma * (255 * N.epsilon⁻¹ / 256))) ∧
                  ∃ kappa : ℝ, (kappa = 1 ∨ kappa = -1) ∧
                    0 < kappa * neckGraphHeight N' f N'.center ∧
                    (∀ x ∈ neckSignedRegion N sigma
                      (127 * N.epsilon⁻¹ / 128) N.epsilon⁻¹,
                      (0 < kappa * neckGraphHeight N' f x ↔
                        255 * N.epsilon⁻¹ / 256 < sigma * (N.coordinate_inverse x).2) ∧
                      (kappa * neckGraphHeight N' f x < 0 ↔
                        sigma * (N.coordinate_inverse x).2 < 255 * N.epsilon⁻¹ / 256)) ∧
                    MapsTo γ (Icc v c) N'.carrier ∧
                    kappa * neckGraphHeight N' f (γ v) < 0 ∧
                    0 < kappa * neckGraphHeight N' f (γ c) ∧
                    (∃ t ∈ Ioo v c, γ t ∈ range (fun p : UnitTwoSphere =>
                      N.coordinate_map (p, sigma * (255 * N.epsilon⁻¹ / 256)))) ∧
                    ∀ (η : ℝ → M) (a b : ℝ), a ≤ b →
                      ContinuousOn η (Icc a b) → MapsTo η (Icc a b) N'.carrier →
                      kappa * neckGraphHeight N' f (η a) < 0 →
                      0 < kappa * neckGraphHeight N' f (η b) →
                      ∃ t ∈ Ioo a b, η t ∈ range (fun p : UnitTwoSphere =>
                        N.coordinate_map (p, sigma * (255 * N.epsilon⁻¹ / 256))) := by
  obtain ⟨epsilonC, hCpos, hCsmall, hcapture⟩ :=
    exists_neck_narrow_region_capture_accuracy.{u}
  obtain ⟨epsilonG, hGpos, _, hgraph⟩ := exists_buffered_neck_sphere_graph_accuracy.{u}
  refine ⟨min epsilonC epsilonG, lt_min hCpos hGpos,
    (min_le_left _ _).trans hCsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g D N N' heq hsmall γ s c hsc hγ hγs hγc hinside hfront
  let A := N.epsilon⁻¹
  have hA : 0 < A := inv_pos.mpr N.epsilon_pos
  have hout : N'.center ∉ N.carrier := by
    rw [frontier, N.carrier_open.interior_eq] at hfront
    exact hfront.2
  have hγout : γ c ∉ N.carrier := by simpa only [hγc] using hout
  obtain ⟨sigma, hsigma, w, hw, hwlevel, hwafter⟩ :=
    exists_signed_level_before_neck_exit N hsc hγ hγs hinside hγout
      (show 0 < 511 * A / 512 by positivity)
      (show 511 * A / 512 < N.epsilon⁻¹ by change 511 * A / 512 < A; linarith)
  have hsignmem (t : ℝ) (ht : t ∈ Ico s c) :
      sigma * (N.coordinate_inverse (γ t)).2 ∈ Ioo (-A) A :=
    neck_signed_axis_mem N hsigma (hinside ht)
  have haxis : ContinuousOn
      (fun t => sigma * (N.coordinate_inverse (γ t)).2) (Icc s w) :=
    continuousOn_const.mul (continuous_snd.comp_continuousOn
      (N.coordinate_inverse_smooth.continuousOn.comp
        (hγ.mono (Icc_subset_Icc le_rfl hw.2.le))
        (fun t ht => hinside ⟨ht.1, ht.2.trans_lt hw.2⟩)))
  have hzero : sigma * (N.coordinate_inverse (γ s)).2 = 0 := by
    rw [hγs, (N.mem_central_sphere_iff_of_mem_carrier
      (N.central_sphere_subset N.center_on_central_sphere)).mp N.center_on_central_sphere,
      mul_zero]
  obtain ⟨v, hv, hvlevel, hvafter⟩ := exists_last_eq_of_continuousOn hw.1.le haxis
    (show sigma * (N.coordinate_inverse (γ s)).2 ≤ 509 * A / 512 by
      rw [hzero]; positivity)
    (show 509 * A / 512 < sigma * (N.coordinate_inverse (γ w)).2 by
      rw [hwlevel]; linarith)
  have hsv : s < v := lt_of_le_of_ne hv.1 (by
    intro he
    subst v
    rw [hzero] at hvlevel
    linarith)
  have hvc : v < c := hv.2.trans_lt hw.2
  have hafter (t : ℝ) (ht : t ∈ Ioo v c) :
      509 * A / 512 < sigma * (N.coordinate_inverse (γ t)).2 := by
    by_cases htw : t ≤ w
    · exact hvafter t ⟨ht.1, htw⟩
    · have h := hwafter t ⟨lt_of_not_ge htw, ht.2⟩
      linarith
  have houtermap : MapsTo γ (Ioo w c) (neckSignedRegion N sigma (255 * A / 256) A) := by
    intro t ht
    have htc : t ∈ Ico s c := ⟨hw.1.le.trans ht.1.le, ht.2⟩
    refine ⟨hinside htc, ?_, (hsignmem t htc).2⟩
    have h := hwafter t ht
    linarith
  have hcclosure : c ∈ closure (Ioo w c) := by
    rw [closure_Ioo hw.2.ne]
    exact right_mem_Icc.mpr hw.2.le
  have hcloseO : N'.center ∈ closure (neckSignedRegion N sigma (255 * A / 256) A) := by
    have h := ((hγ c (right_mem_Icc.mpr hsc.le)).mono
      (fun t (ht : t ∈ Ioo w c) => ⟨hw.1.le.trans ht.1.le, ht.2.le⟩)).mem_closure
        hcclosure houtermap
    simpa only [hγc] using h
  have hOT : neckSignedRegion N sigma (255 * A / 256) A ⊆
      neckSignedRegion N sigma (127 * A / 128) A := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2.1], hx.2.2⟩
  have hcloseT := closure_mono hOT hcloseO
  have hcap : neckSignedRegion N sigma (127 * A / 128) A ⊆
      N'.region (-(N'.epsilon⁻¹ / 2)) (N'.epsilon⁻¹ / 2) := by
    rcases hsigma with hs | hs
    · rw [hs, neckSignedRegion_one] at hcloseT ⊢
      exact (hcapture M g D N N' heq (hsmall.trans (min_le_left _ _))
        (127 * A / 128) A (by change A - 127 * A / 128 ≤ A / 128; linarith)
        hcloseT).2
    · rw [hs, neckSignedRegion_neg_one] at hcloseT ⊢
      exact (hcapture M g D N N' heq (hsmall.trans (min_le_left _ _))
        (-A) (-(127 * A / 128))
        (by change -(127 * A / 128) - -A ≤ A / 128; linarith) hcloseT).2
  have ha : sigma * (255 * A / 256) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    change -A < sigma * (255 * A / 256) ∧ sigma * (255 * A / 256) < A
    rcases hsigma with rfl | rfl <;> constructor <;> nlinarith
  have hS (p : UnitTwoSphere) :
      N.coordinate_map (p, sigma * (255 * A / 256)) ∈
        neckSignedRegion N sigma (127 * A / 128) A := by
    have hN := N.coordinate_map_mem (z := (p, sigma * (255 * A / 256)))
      ⟨mem_univ p, ha⟩
    have hz := (mem_neck_slice_iff_signed_axis N hsigma ha hN).mp ⟨p, rfl⟩
    exact ⟨hN, by rw [hz]; linarith, by rw [hz]; linarith⟩
  let p0 : UnitTwoSphere := (N.coordinate_inverse N.center).1
  have hp0 := hcap (hS p0)
  have hNgraph : N.epsilon ≤ epsilonG := hsmall.trans (min_le_right _ _)
  have hN'graph : N'.epsilon ≤ epsilonG := heq ▸ hNgraph
  obtain ⟨phi, hphi, f, hf, hbuffer, hpoint, hrange⟩ := hgraph M g D N' N
    hN'graph hNgraph (sigma * (255 * A / 256)) ha p0 hp0.1
    (by apply abs_le.mpr; constructor <;> linarith [hp0.2.1, hp0.2.2,
      inv_pos.mpr N'.epsilon_pos])
  have hfdom (p : UnitTwoSphere) : f p ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ := by
    have h := abs_lt.mp (hbuffer p)
    constructor <;> linarith [h.1, h.2, inv_pos.mpr N'.epsilon_pos]
  have hiso : SmoothSphereIsotopicIn N.carrier
      (range (fun p : UnitTwoSphere => N.coordinate_map (p, sigma * (255 * A / 256))))
      N.central_sphere :=
    neck_graph_isotopic_central N (fun _ => sigma * (255 * A / 256))
      contMDiff_const (fun _ => ha)
  have hiso' : SmoothSphereIsotopicIn N'.carrier
      (range (fun p : UnitTwoSphere => N.coordinate_map (p, sigma * (255 * A / 256))))
      N'.central_sphere := by
    rw [hrange]
    exact neck_graph_isotopic_central N' f hf hfdom
  have hzeroS (x : M) (hx : x ∈ N'.carrier) : neckGraphHeight N' f x = 0 ↔
      x ∈ range (fun p : UnitTwoSphere => N.coordinate_map (p, sigma * (255 * A / 256))) := by
    rw [hrange]
    exact neckGraphHeight_eq_zero_iff N' hfdom hx
  obtain ⟨hminus, hplus, hdisjoint, hunion⟩ := neckGraphHeight_sides N' hf hfdom
  rw [← hrange] at hunion
  obtain ⟨kappa, hkappa, hpcenter, halign⟩ := neck_graph_side_alignment N N' hsigma
    (lo := 127 * A / 128) (a := 255 * A / 256) (hi := A)
    (by change -A ≤ 127 * A / 128; linarith) le_rfl (by linarith) (by linarith)
    hf hfdom hrange (fun x hx => (hcap hx).1) hcloseO hout
  have hvT : γ v ∈ neckSignedRegion N sigma (127 * A / 128) A := by
    exact ⟨hinside ⟨hsv.le, hvc⟩, by rw [hvlevel]; linarith,
      (hsignmem v ⟨hsv.le, hvc⟩).2⟩
  have hγN' : MapsTo γ (Icc v c) N'.carrier := by
    intro t ht
    by_cases htc : t = c
    · subst t
      rw [hγc]
      exact N'.central_sphere_subset N'.center_on_central_sphere
    · have htlt : t < c := lt_of_le_of_ne ht.2 htc
      by_cases htv : t = v
      · subst t
        exact (hcap hvT).1
      · have hvlt : v < t := lt_of_le_of_ne ht.1 (Ne.symm htv)
        exact (hcap ⟨hinside ⟨hsv.le.trans ht.1, htlt⟩,
          by linarith [hafter t ⟨hvlt, htlt⟩],
          (hsignmem t ⟨hsv.le.trans ht.1, htlt⟩).2⟩).1
  have hvneg : kappa * neckGraphHeight N' f (γ v) < 0 :=
    (halign (γ v) hvT).2.mpr (by rw [hvlevel]; linarith)
  have hcpos : 0 < kappa * neckGraphHeight N' f (γ c) := by
    simpa only [hγc] using hpcenter
  have hcross : ∀ (η : ℝ → M) (a b : ℝ), a ≤ b →
      ContinuousOn η (Icc a b) → MapsTo η (Icc a b) N'.carrier →
      kappa * neckGraphHeight N' f (η a) < 0 →
      0 < kappa * neckGraphHeight N' f (η b) →
      ∃ t ∈ Ioo a b, η t ∈ range (fun p : UnitTwoSphere =>
        N.coordinate_map (p, sigma * (255 * A / 256))) := by
    intro η a b hab hη hηN hneg hpos
    rw [hrange]
    exact exists_neck_graph_crossing N' hf hfdom hab hη hηN hkappa hneg hpos
  refine ⟨sigma, hsigma, v, ⟨hsv, hvc⟩, hvlevel, hafter, hcloseT, hcloseO, hcap,
    phi, hphi, f, hf, hbuffer, hpoint, hrange, hiso, hiso',
    continuousOn_neckGraphHeight N' hf, hzeroS, hminus, hplus, hdisjoint, hunion,
    kappa, hkappa, hpcenter, halign, hγN', hvneg, hcpos, ?_, hcross⟩
  exact hcross γ v c hvc.le (hγ.mono (Icc_subset_Icc hsv.le le_rfl)) hγN' hvneg hcpos

end PoincareConjecture.M28
