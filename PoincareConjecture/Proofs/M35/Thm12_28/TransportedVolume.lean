import PoincareConjecture.Proofs.M35.Thm12_28.TransportedBall
import PoincareConjecture.Proofs.M10.InverseMeasure
import PoincareConjecture.Proofs.M10.MeasureGluing










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

namespace PoincareConjecture.M35

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]

private theorem edist_image_le_on_inner_ball
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N) (f : M → N)
    {U : Set M} (hU : IsOpen U) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    {C : ℝ≥0} (hbound : ∀ z ∈ U, ∀ v : TangentSpace (𝓡 3) z,
      h.tangentNorm (f z) (mfderiv (𝓡 3) (𝓡 3) f z v) ≤ C * g.tangentNorm z v)
    {x₀ x y : M} {r : ℝ≥0}
    (hball : ∀ z, g.edist x₀ z < (r : ℝ≥0∞) + r + r → z ∈ U)
    (hx : g.edist x₀ x < r) (hy : g.edist x₀ y < r) :
    h.edist (f x) (f y) ≤ (C : ℝ≥0∞) * g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  have hd : g.edist x y < (r : ℝ≥0∞) + r := by
    calc
      g.edist x y ≤ g.edist x x₀ + g.edist x₀ y := Manifold.riemannianEDist_triangle
      _ < (r : ℝ≥0∞) + r := ENNReal.add_lt_add
        (by simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_comm] using hx) hy
  let : (𝓝[>] (g.edist x y)).NeBot := nhdsGT_neBot_of_exists_gt ⟨_, hd⟩
  have hlim : Tendsto (fun R : ℝ≥0∞ => (C : ℝ≥0∞) * R)
      (𝓝[>] (g.edist x y)) (𝓝 ((C : ℝ≥0∞) * g.edist x y)) :=
    (ENNReal.continuous_const_mul ENNReal.coe_ne_top).continuousWithinAt
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds hd)] with R hR hRsmall
  obtain ⟨gamma, hstart, hend, hsmooth, hlength, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (I := 𝓡 3) hR zero_lt_one
  have hmaps : MapsTo gamma (Icc (0 : ℝ) 1) U := by
    intro s hs
    apply hball
    have hprefix : g.edist x (gamma s) ≤ g.pathELength gamma 0 1 :=
      (Manifold.riemannianEDist_le_pathELength hsmooth.contMDiffOn hstart rfl hs.1).trans
        (Manifold.pathELength_mono le_rfl hs.2)
    calc
      g.edist x₀ (gamma s) ≤ g.edist x₀ x + g.edist x (gamma s) :=
        Manifold.riemannianEDist_triangle
      _ ≤ g.edist x₀ x + g.pathELength gamma 0 1 := add_le_add_right hprefix _
      _ < (r : ℝ≥0∞) + (r + r) := ENNReal.add_lt_add hx (hlength.trans hRsmall)
      _ = (r : ℝ≥0∞) + r + r := (add_assoc _ _ _).symm
  have himage : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (f ∘ gamma) (Icc 0 1) :=
    (hf.of_le (by simp)).comp hsmooth.contMDiffOn hmaps
  have hdist : h.edist (f x) (f y) ≤ h.pathELength (f ∘ gamma) 0 1 :=
    Manifold.riemannianEDist_le_pathELength himage (congrArg f hstart)
      (congrArg f hend) zero_le_one
  have hpath := pathELength_comp_le_of_tangentNorm_le g h f hU hf C.coe_nonneg
    hbound gamma 0 1 hsmooth.contMDiffOn hmaps
  rw [ENNReal.ofReal_coe_nnreal] at hpath
  exact hdist.trans (hpath.trans (mul_le_mul' le_rfl hlength.le))




theorem calibratedVolume_image_le_of_tangentNorm_le
    [T3Space M] [T3Space N] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    {U : Set M} (hU : IsOpen U) (hUsource : U ⊆ phi.source) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ U, ∀ v : TangentSpace (𝓡 3) z,
      h.tangentNorm (phi z) (mfderiv (𝓡 3) (𝓡 3) phi z v) ≤ C * g.tangentNorm z v)
    {A : Set M} (hA : MeasurableSet A) (hAU : A ⊆ U) :
    calibratedMetricVolume h (phi '' A) ≤
      ENNReal.ofReal (C ^ 3) * calibratedMetricVolume g A := by
  let : EMetricSpace M := g.toEMetricSpace
  let : EMetricSpace N := h.toEMetricSpace
  let c : ℝ≥0 := ⟨C, hC⟩
  let mu := ((calibratedMetricVolume h).restrict phi.target).map phi.invFun
  have hlocal : ∀ x ∈ U, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∀ B : Set M, MeasurableSet B → B ⊆ V →
        mu B ≤ ENNReal.ofReal (C ^ 3) * calibratedMetricVolume g B := by
    intro x hx
    obtain ⟨epsilon, hepsilon, hsmall⟩ := EMetric.mem_nhds_iff.mp
      (hU.mem_nhds hx)
    obtain ⟨r, hr, hrsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt
      (a := (3 : ℝ≥0∞)) (by norm_num) hepsilon.ne'
    have htriple : (r : ℝ≥0∞) + r + r < epsilon := by
      convert hrsmall using 1
      ring
    have hball : ∀ z, g.edist x z < (r : ℝ≥0∞) + r + r → z ∈ U := by
      intro z hz
      apply hsmall
      change edist z x < epsilon
      rw [edist_comm]
      exact hz.trans htriple
    let V := {z : M | g.edist x z < (r : ℝ≥0∞)}
    have hV : IsOpen V := isOpen_lt (continuous_const.edist continuous_id) continuous_const
    have hxV : x ∈ V := by
      change edist x x < (r : ℝ≥0∞)
      simpa only [edist_self] using (ENNReal.coe_pos.mpr hr)
    have hVU : V ⊆ U := by
      intro z hz
      apply hball z
      exact hz.trans_le ((le_add_of_nonneg_right (show 0 ≤ (r : ℝ≥0∞) from bot_le)).trans
        (le_add_of_nonneg_right (show 0 ≤ (r : ℝ≥0∞) from bot_le)))
    have hlip : LipschitzOnWith c phi V := by
      intro y hy z hz
      exact edist_image_le_on_inner_ball g h phi hU
        (phi.contMDiffOn_toFun.mono hUsource) (C := c) hbound hball hy hz
    refine ⟨V, hV, hxV, ?_⟩
    intro B hB hBV
    have hmeasure : mu B = calibratedMetricVolume h (phi '' B) :=
      M10.map_inverse_restrict_apply phi.toOpenPartialHomeomorph
        (calibratedMetricVolume h) hB ((hBV.trans hVU).trans hUsource)
    rw [hmeasure]
    have hhaus := (hlip.mono hBV).hausdorffMeasure_image_le (d := (3 : ℝ)) (by norm_num)
    rw [show (c : ℝ≥0∞) ^ (3 : ℝ) = (c : ℝ≥0∞) ^ (3 : ℕ) from
      ENNReal.rpow_natCast _ _] at hhaus
    have hfactor : (c : ℝ≥0∞) ^ 3 = ENNReal.ofReal (C ^ 3) := by
      rw [ENNReal.ofReal_pow hC]
      exact congrArg (fun a : ℝ≥0∞ => a ^ (3 : ℕ)) ENNReal.ofReal_coe_nnreal.symm
    rw [hfactor] at hhaus
    change euclideanVolumeCalibration 3 * Measure.hausdorffMeasure (3 : ℝ) (phi '' B) ≤
      ENNReal.ofReal (C ^ 3) *
        (euclideanVolumeCalibration 3 * Measure.hausdorffMeasure (3 : ℝ) B)
    exact (mul_le_mul' le_rfl hhaus).trans_eq (mul_left_comm _ _ _)
  have hglobal := M10.measure_le_mul_of_local_comparison hlocal hA hAU
  have hmeasure : mu A = calibratedMetricVolume h (phi '' A) :=
    M10.map_inverse_restrict_apply phi.toOpenPartialHomeomorph
      (calibratedMetricVolume h) hA (hAU.trans hUsource)
  exact hmeasure ▸ hglobal




theorem calibratedVolume_le_image_of_tangentNorm_lower
    [T3Space M] [T3Space N] [SecondCountableTopology N]
    [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞)
    {U : Set M} (hU : IsOpen U) (hUsource : U ⊆ phi.source) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z ∈ U, ∀ v : TangentSpace (𝓡 3) z,
      g.tangentNorm z v ≤ C * h.tangentNorm (phi z) (mfderiv (𝓡 3) (𝓡 3) phi z v))
    {A : Set M} (hA : IsOpen A) (hAU : A ⊆ U) :
    calibratedMetricVolume g A ≤
      ENNReal.ofReal (C ^ 3) * calibratedMetricVolume h (phi '' A) := by
  let psi : PartialDiffeomorph (𝓡 3) (𝓡 3) M N ∞ := {
    toPartialEquiv := phi.toPartialEquiv.restr U
    open_source := phi.open_source.inter hU
    open_target := (phi.toOpenPartialHomeomorph.restrOpen U hU).open_target
    contMDiffOn_toFun := phi.contMDiffOn_toFun.mono inter_subset_left
    contMDiffOn_invFun := phi.contMDiffOn_invFun.mono inter_subset_left
  }
  have hAsource : A ⊆ psi.source := fun _ hx => ⟨hUsource (hAU hx), hAU hx⟩
  have himage : IsOpen (psi '' A) :=
    psi.toOpenPartialHomeomorph.isOpen_image_of_subset_source hA hAsource
  have htarget : psi '' A ⊆ psi.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact psi.map_source (hAsource hz)
  have hinverse := inverse_tangentNorm_bound g h psi C
    (fun z hz => hbound z hz.2)
  have hvolume := calibratedVolume_image_le_of_tangentNorm_le h g psi.symm
    psi.open_target Subset.rfl hC hinverse himage.measurableSet htarget
  have heq : psi.invFun '' (psi '' A) = A := by
    rw [image_image]
    apply subset_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hleft : psi.invFun (psi z) = z := psi.left_inv (hAsource hz)
      change psi.invFun (psi z) ∈ A
      rwa [hleft]
    · intro z hz
      exact ⟨z, hz, psi.left_inv (hAsource hz)⟩
  change calibratedMetricVolume g (psi.invFun '' (psi '' A)) ≤
    ENNReal.ofReal (C ^ 3) * calibratedMetricVolume h (phi '' A) at hvolume
  rwa [heq] at hvolume

end PoincareConjecture.M35
