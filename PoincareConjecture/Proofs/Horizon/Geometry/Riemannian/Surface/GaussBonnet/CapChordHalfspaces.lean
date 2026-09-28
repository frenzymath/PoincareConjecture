import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CapSectorGerms
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Triangles.CapSeparation
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Collars.CoreCapIntersections

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open Poincare.Topology.Plane.Meshes Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

private theorem transverse_sign_radius {f : ℝ × ℝ → ℝ}
    (hf : ContDiffAt ℝ 1 f 0)
    (hdf : HasFDerivAt f (ContinuousLinearMap.fst ℝ ℝ ℝ) 0)
    (hzero : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), q.1 = 0 → f q = 0) :
    ∃ δ > 0, ∀ r t : ℝ, |r| < δ → |t| < δ →
      (0 < f (r, t) ↔ 0 < r) ∧ (f (r, t) = 0 ↔ r = 0) := by
  let K : ℝ × (ℝ × ℝ) → ℝ × ℝ := fun p => (f p.2, p.2.2)
  have hK : ContDiffAt ℝ 1 K (0, (0, 0)) :=
    (hf.comp (0, (0, 0)) contDiffAt_snd).prodMk contDiffAt_snd.snd
  have hdS : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => p.2)
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) (0, (0, 0)) := hasFDerivAt_snd
  have hdK : HasFDerivAt K (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) (0, (0, 0)) := by
    convert! (hdf.comp (0, (0, 0)) hdS).prodMk hdS.snd using 1
  have haxes : ∀ᶠ p in 𝓝 ((0 : ℝ), ((0 : ℝ), (0 : ℝ))),
      (p.2.1 = 0 → (K p).1 = 0) ∧ (p.2.2 = 0 → (K p).2 = 0) := by
    filter_upwards [continuousAt_snd.tendsto.eventually hzero] with p hp
    exact ⟨hp, id⟩
  obtain ⟨δ, hδ, hsign⟩ := Poincare.Analysis.exists_quadrant_preserving_radius hK hdK haxes
  exact ⟨δ, hδ, fun r t hr ht =>
    ⟨(hsign 0 r t (by simpa using hδ) hr ht).1.1,
      (hsign 0 r t (by simpa using hδ) hr ht).1.2.1⟩⟩

theorem exists_affine_halfspace_of_regular_line
    {g : Plane → ℝ} {a v d : Plane}
    (hg : ContDiffAt ℝ 1 g a)
    (hind : LinearIndependent ℝ (![v, d] : Fin 2 → Plane))
    (hv : fderiv ℝ g a v = 1) (hd : fderiv ℝ g a d = 0)
    (hzero : ∀ᶠ t in 𝓝 (0 : ℝ), g (a + t • d) = 0) :
    ∃ ℓ : Plane →ᵃ[ℝ] ℝ, Function.Surjective ℓ ∧ ℓ a = 0 ∧
      ℓ.linear v = 1 ∧ ℓ.linear d = 0 ∧
      ∀ᶠ z in 𝓝 a, (0 < g z ↔ 0 < ℓ z) ∧ (g z = 0 ↔ ℓ z = 0) ∧
        (g z ≤ 0 ↔ ℓ z ≤ 0) := by
  let b := basisOfLinearIndependentOfCardEqFinrank hind (by simp)
  let L := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    b.equivFun.toContinuousLinearEquiv.symm
  have hL (q : ℝ × ℝ) : L q = q.1 • v + q.2 • d := by
    change b.equivFun.symm ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm q) = _
    rw [Module.Basis.equivFun_symm_apply]
    simp [b, Fin.sum_univ_succ, coe_basisOfLinearIndependentOfCardEqFinrank]
  let H : ℝ × ℝ → Plane := fun q => a + L q
  have hH0 : H 0 = a := by simp [H]
  have hdH : HasFDerivAt H L.toContinuousLinearMap 0 := by
    convert! (L.toContinuousLinearMap.hasFDerivAt (x := (0 : ℝ × ℝ))).const_add a using 1
  have hdg : HasFDerivAt g (fderiv ℝ g a) (H 0) := by
    simpa only [hH0] using hg.differentiableAt_one.hasFDerivAt
  have hdf : HasFDerivAt (g ∘ H) (ContinuousLinearMap.fst ℝ ℝ ℝ) 0 := by
    have he : (fderiv ℝ g a).comp L.toContinuousLinearMap =
        ContinuousLinearMap.fst ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro q
      change (fderiv ℝ g a) (L q) = q.1
      simp [hL, hv, hd]
    convert! hdg.comp 0 hdH using 1
    exact he.symm
  have hcomp : ContDiffAt ℝ 1 (g ∘ H) 0 := by
    apply ContDiffAt.comp _ _ (contDiffAt_const.add L.contDiff.contDiffAt)
    simpa only [map_zero, add_zero] using hg
  have hz : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), q.1 = 0 → (g ∘ H) q = 0 := by
    filter_upwards [continuousAt_snd.tendsto.eventually hzero] with q hq hq0
    simpa [H, hL, hq0] using hq
  obtain ⟨δ, hδ, hsign⟩ := transverse_sign_radius hcomp hdf hz
  let A : Plane →ₗ[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toLinearMap.comp L.symm.toLinearEquiv.toLinearMap
  let ℓ : Plane →ᵃ[ℝ] ℝ := A.toAffineMap - AffineMap.const ℝ Plane (A a)
  have hℓ (z : Plane) : ℓ z = (L.symm (z - a)).1 := by
    simp [ℓ, A, map_sub]
  have hvL : L (1, 0) = v := by simp [hL]
  have hdL : L (0, 1) = d := by simp [hL]
  refine ⟨ℓ, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    refine ⟨a + L (s, 0), ?_⟩
    simp [hℓ]
  · simp [hℓ]
  · simp only [ℓ, AffineMap.sub_linear, LinearMap.toAffineMap_linear,
      AffineMap.const_linear, sub_zero]
    change (L.symm v).1 = 1
    rw [← hvL, L.symm_apply_apply]
  · simp only [ℓ, AffineMap.sub_linear, LinearMap.toAffineMap_linear,
      AffineMap.const_linear, sub_zero]
    change (L.symm d).1 = 0
    rw [← hdL, L.symm_apply_apply]
  · have hcoord : ContinuousAt (fun z : Plane => L.symm (z - a)) a := by fun_prop
    have hcoord0 : L.symm (a - a) = 0 := by simp
    have hbox : {q : ℝ × ℝ | |q.1| < δ ∧ |q.2| < δ} ∈ 𝓝 (0 : ℝ × ℝ) := by
      apply IsOpen.mem_nhds
      · change IsOpen ({q : ℝ × ℝ | |q.1| < δ} ∩ {q : ℝ × ℝ | |q.2| < δ})
        exact (isOpen_lt (by fun_prop) continuous_const).inter
          (isOpen_lt (by fun_prop) continuous_const)
      · simpa using And.intro hδ hδ
    have hev : ∀ᶠ z in 𝓝 a, |(L.symm (z - a)).1| < δ ∧
        |(L.symm (z - a)).2| < δ := by
      have h := hcoord.tendsto.eventually (hcoord0 ▸ hbox)
      exact h
    filter_upwards [hev] with z hz
    have hs := hsign (L.symm (z - a)).1 (L.symm (z - a)).2 hz.1 hz.2
    have he : H ((L.symm (z - a)).1, (L.symm (z - a)).2) = z := by
      change a + L (L.symm (z - a)) = z
      rw [L.apply_symm_apply]
      abel
    dsimp only [Function.comp_apply] at hs
    rw [he, ← hℓ] at hs
    exact ⟨hs.1, hs.2, le_iff_le_iff_lt_iff_lt.mpr hs.1⟩

theorem exists_cap_chord_excess_affine_germ
    (F : OpenPartialHomeomorph (ℝ × ℝ) Plane)
    (hF : ContDiffOn ℝ ∞ F F.source) (hI : ContDiffOn ℝ ∞ F.symm F.target)
    {ε : ℝ} (hε : 0 < ε)
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ ε} ⊆ F.source)
    (hchord : ∀ t : ℝ, F ((1 - t) * ε, t * ε) =
      (1 - t) • F (ε, 0) + t • F (0, ε))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let a := (1 - t) • F (ε, 0) + t • F (0, ε)
    ∃ ℓ : Plane →ᵃ[ℝ] ℝ, Function.Surjective ℓ ∧ ℓ a = 0 ∧
      ℓ.linear (F (0, ε) - F (ε, 0)) = 0 ∧
      ∀ᶠ z in 𝓝 a, (0 < capExcess F ε z ↔ 0 < ℓ z) ∧
        (capExcess F ε z = 0 ↔ ℓ z = 0) ∧ (capExcess F ε z ≤ 0 ↔ ℓ z ≤ 0) := by
  let q : ℝ × ℝ := ((1 - t) * ε, t * ε)
  let a := F q
  let v := fderiv ℝ F q (1, 0)
  let d := F (0, ε) - F (ε, 0)
  have hq : q ∈ F.source := hsource
    ⟨mul_nonneg (sub_nonneg.mpr ht.2) hε.le, mul_nonneg ht.1 hε.le, by nlinarith⟩
  have hdF := ((hF q hq).contDiffAt (F.open_source.mem_nhds hq)).differentiableAt
    (by simp) |>.hasFDerivAt
  have hInv := (hI (F q) (F.map_source hq)).contDiffAt
    (F.open_target.mem_nhds (F.map_source hq))
  have hdI := hInv.differentiableAt (by simp) |>.hasFDerivAt
  have hleft : Function.LeftInverse (fderiv ℝ F.symm (F q)) (fderiv ℝ F q) := by
    have he := (hdI.comp q hdF).unique
      ((hasFDerivAt_id q).congr_of_eventuallyEq (F.eventually_left_inverse hq))
    intro w
    exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) => L w) he
  have hdcap : HasFDerivAt (capExcess F ε)
      (((ContinuousLinearMap.fst ℝ ℝ ℝ) + ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (fderiv ℝ F.symm (F q))) (F q) := by
    convert! (hdI.fst.add hdI.snd).sub_const ε using 1
  have hcap : ContDiffAt ℝ 1 (capExcess F ε) a :=
    ((hInv.fst.add hInv.snd).sub contDiffAt_const).of_le (by simp)
  have hv : fderiv ℝ (capExcess F ε) a v = 1 := by
    rw [hdcap.fderiv]
    change (fderiv ℝ F.symm (F q) (fderiv ℝ F q (1, 0))).1 +
      (fderiv ℝ F.symm (F q) (fderiv ℝ F q (1, 0))).2 = 1
    rw [hleft]
    norm_num
  have hfd : fderiv ℝ F q (-ε, ε) = d :=
    cap_chord_fderiv F hF hε hsource (fun s _ => hchord s) ht
  have hd : fderiv ℝ (capExcess F ε) a d = 0 := by
    rw [hdcap.fderiv, ← hfd]
    change (fderiv ℝ F.symm (F q) (fderiv ℝ F q (-ε, ε))).1 +
      (fderiv ℝ F.symm (F q) (fderiv ℝ F q (-ε, ε))).2 = 0
    rw [hleft]
    simp
  have hind₀ : LinearIndependent ℝ (![((1 : ℝ), (0 : ℝ)), (-ε, ε)] : Fin 2 → ℝ × ℝ) := by
    rw [linearIndependent_fin2]
    constructor
    · intro h
      exact hε.ne' (congrArg Prod.snd h)
    · intro c h
      have hcε : c * ε = 0 := congrArg Prod.snd h
      have hc : c = 0 := (mul_eq_zero.mp hcε).resolve_right hε.ne'
      have he := congrArg Prod.fst h
      simp [hc] at he
  have hind : LinearIndependent ℝ (![v, d] : Fin 2 → Plane) := by
    rw [← hfd]
    convert hind₀.map_injOn (fderiv ℝ F q).toLinearMap hleft.injective.injOn using 1
    ext k
    fin_cases k <;> rfl
  let path : ℝ → ℝ × ℝ := fun s => ((1 - (t + s)) * ε, (t + s) * ε)
  have hpath : Continuous path := by dsimp [path]; fun_prop
  have hpath0 : path 0 = q := by simp [path, q]
  have hpathsource : ∀ᶠ s in 𝓝 (0 : ℝ), path s ∈ F.source :=
    hpath.continuousAt.eventually (F.open_source.mem_nhds (by rwa [hpath0]))
  have hline (s : ℝ) : F (path s) = a + s • d := by
    dsimp [path, a, q, d]
    rw [hchord, hchord]
    module
  have hzero : ∀ᶠ s in 𝓝 (0 : ℝ), capExcess F ε (a + s • d) = 0 := by
    filter_upwards [hpathsource] with s hs
    rw [← hline, capExcess, F.left_inv hs]
    dsimp [path]
    ring
  obtain ⟨ℓ, hsurj, ha, -, hld, hsign⟩ :=
    exists_affine_halfspace_of_regular_line hcap hind hv hd hzero
  have haeq : a = (1 - t) • F (ε, 0) + t • F (0, ε) := hchord t
  exact ⟨ℓ, hsurj, haeq ▸ ha, hld, haeq ▸ hsign⟩

theorem affine_functionals_eq_smul_of_common_line
    (f ℓ : Plane →ᵃ[ℝ] ℝ) (hf : Function.Surjective f) (hℓ : Function.Surjective ℓ)
    {a d : Plane} (hd : d ≠ 0) (hfa : f a = 0) (hℓa : ℓ a = 0)
    (hfd : f.linear d = 0) (hℓd : ℓ.linear d = 0) :
    ∃ c : ℝ, c ≠ 0 ∧ ℓ = c • f := by
  obtain ⟨z₀, hz₀⟩ := hf 1
  let v := z₀ - a
  have hfv : f.linear v = 1 := by
    change f.linear (z₀ -ᵥ a) = 1
    rw [f.linearMap_vsub, vsub_eq_sub, hz₀, hfa, sub_zero]
  have hind : LinearIndependent ℝ (![v, d] : Fin 2 → Plane) := by
    rw [linearIndependent_fin2]
    refine ⟨hd, ?_⟩
    intro s he
    have h := congrArg f.linear he
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      map_smul, hfd, smul_zero, hfv] at h
    exact one_ne_zero h.symm
  let b := basisOfLinearIndependentOfCardEqFinrank hind (by simp)
  have hrep (z : Plane) : z - a = (b.repr (z - a) 0) • v + (b.repr (z - a) 1) • d := by
    have h := b.sum_repr (z - a)
    simpa only [Fin.sum_univ_two, b, coe_basisOfLinearIndependentOfCardEqFinrank,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h.symm
  have hfz (z : Plane) : f z = b.repr (z - a) 0 := by
    have h := congrArg f.linear (hrep z)
    have he : f.linear (z - a) = f z := by
      change f.linear (z -ᵥ a) = f z
      rw [f.linearMap_vsub, vsub_eq_sub, hfa, sub_zero]
    simpa only [he, map_add, map_smul, hfv, hfd, smul_eq_mul, mul_one, mul_zero,
      add_zero] using h
  have hℓz (z : Plane) : ℓ z = ℓ.linear v * f z := by
    have h := congrArg ℓ.linear (hrep z)
    have he : ℓ.linear (z - a) = ℓ z := by
      change ℓ.linear (z -ᵥ a) = ℓ z
      rw [ℓ.linearMap_vsub, vsub_eq_sub, hℓa, sub_zero]
    simpa only [he, map_add, map_smul, hℓd, smul_eq_mul, mul_zero, zero_mul, add_zero,
      ← hfz, mul_comm] using h
  refine ⟨ℓ.linear v, ?_, ?_⟩
  · intro hzero
    obtain ⟨z, hz⟩ := hℓ 1
    have h := hℓz z
    rw [hzero, zero_mul, hz] at h
    exact one_ne_zero h
  · ext z
    exact hℓz z

namespace ChartCircleArrangementVertexPatch.VertexCapFaces

variable {S : Type*} [TopologicalSpace S] [T2Space S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {r : S → ℝ} {p : S} {P : ChartCircleArrangementVertexPatch r p}
  {x : Bool × Bool → S} (B : VertexCapFaces P x)

theorem exists_chart_carrier_chord_affine_halfspace (i : Bool × Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    let a := (1 - t) • B.planarCoordinates i (B.scale, 0) +
      t • B.planarCoordinates i (0, B.scale)
    ∃ ℓ : Plane →ᵃ[ℝ] ℝ, Function.Surjective ℓ ∧ ℓ a = 0 ∧
      ℓ.linear (B.planarCoordinates i (0, B.scale) -
        B.planarCoordinates i (B.scale, 0)) = 0 ∧
      ∀ᶠ z in 𝓝 a,
        z ∈ chartAt Plane (x i) '' (B.face i).carrier ↔ ℓ z ≤ 0 := by
  obtain ⟨ℓ, hsurj, ha, hd, hsign⟩ := exists_cap_chord_excess_affine_germ
    (B.planarCoordinates i) (B.planar_smooth i) (B.planar_smooth_symm i)
    B.scale_pos (B.planar_source i) (B.planar_chord i) ⟨ht.1.le, ht.2.le⟩
  refine ⟨ℓ, hsurj, ha, hd, ?_⟩
  filter_upwards [B.chart_carrier_chord_eventually_iff i ht, hsign] with z hz hs
  exact hz.trans hs.2.2

theorem planar_chord_direction_ne_zero (i : Bool × Bool) :
    B.planarCoordinates i (0, B.scale) - B.planarCoordinates i (B.scale, 0) ≠ 0 := by
  intro he
  have hp := (B.planarCoordinates i).injOn
    (B.planar_source i ⟨le_rfl, B.scale_pos.le, by simp⟩)
    (B.planar_source i ⟨B.scale_pos.le, le_rfl, by simp⟩) (sub_eq_zero.mp he)
  exact B.scale_pos.ne' (congrArg Prod.snd hp)

theorem chart_carrier_chord_supportingLine_germ (i : Bool × Bool) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    let a := (1 - t) • B.planarCoordinates i (B.scale, 0) +
      t • B.planarCoordinates i (0, B.scale)
    B.chordSupportingLine i a = 0 ∧
      ∃ s : Bool, ∀ᶠ z in 𝓝 a,
        z ∈ chartAt Plane (x i) '' (B.face i).carrier ↔
          0 ≤ (if s then B.chordSupportingLine i z else -B.chordSupportingLine i z) := by
  let a := (1 - t) • B.planarCoordinates i (B.scale, 0) +
    t • B.planarCoordinates i (0, B.scale)
  let d := B.planarCoordinates i (0, B.scale) - B.planarCoordinates i (B.scale, 0)
  let f := B.chordSupportingLine i
  have hfirst : f (B.planarCoordinates i (B.scale, 0)) = 0 := by
    apply (B.chordSupportingLine_spec i).2
    rw [chartChord, B.planar_first i B.scale ⟨B.scale_pos.le, le_rfl⟩]
    exact left_mem_affineSegment ℝ _ _
  have hsecond : f (B.planarCoordinates i (0, B.scale)) = 0 := by
    apply (B.chordSupportingLine_spec i).2
    rw [chartChord, B.planar_second i B.scale ⟨B.scale_pos.le, le_rfl⟩]
    exact right_mem_affineSegment ℝ _ _
  have hfa : f a = 0 := by
    have he : a = AffineMap.lineMap (B.planarCoordinates i (B.scale, 0))
        (B.planarCoordinates i (0, B.scale)) t := by
      simp [a, AffineMap.lineMap_apply_module]
    rw [he, AffineMap.apply_lineMap, hfirst, hsecond]
    simp
  have hfd : f.linear d = 0 := by
    change f.linear (B.planarCoordinates i (0, B.scale) -ᵥ
      B.planarCoordinates i (B.scale, 0)) = 0
    rw [f.linearMap_vsub, vsub_eq_sub, hfirst, hsecond, sub_self]
  obtain ⟨ℓ, hsurj, hℓa, hℓd, hmem⟩ := B.exists_chart_carrier_chord_affine_halfspace i ht
  obtain ⟨c, hc, he⟩ := affine_functionals_eq_smul_of_common_line f ℓ
    (B.chordSupportingLine_spec i).1 hsurj (B.planar_chord_direction_ne_zero i) hfa hℓa hfd hℓd
  refine ⟨hfa, ?_⟩
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · refine ⟨true, ?_⟩
    filter_upwards [hmem] with z hz
    rw [he] at hz
    change _ ↔ c * f z ≤ 0 at hz
    change _ ↔ 0 ≤ f z
    exact hz.trans (by constructor <;> intro h <;> nlinarith)
  · refine ⟨false, ?_⟩
    filter_upwards [hmem] with z hz
    rw [he] at hz
    change _ ↔ c * f z ≤ 0 at hz
    change _ ↔ 0 ≤ -f z
    exact hz.trans (by constructor <;> intro h <;> nlinarith)

end ChartCircleArrangementVertexPatch.VertexCapFaces

end PoincareConjecture.Topology.Surface
