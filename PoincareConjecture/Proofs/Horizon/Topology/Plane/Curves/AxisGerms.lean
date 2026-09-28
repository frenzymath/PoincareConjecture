import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.Coordinates

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Curves

def axisCoordinate (horizontal : Bool) (z : ℝ × ℝ) : ℝ :=
  if horizontal then z.1 else z.2

def signedAxis (horizontal : Bool) (sign u : ℝ) : ℝ × ℝ :=
  if horizontal then (sign * u, 0) else (0, sign * u)

theorem exists_smooth_increasing_inverse
    {g : ℝ → ℝ} (hg : ∀ᶠ t in 𝓝 0, ContDiffAt ℝ ∞ g t)
    (hgzero : g 0 = 0) (hpos : 0 < deriv g 0)
    {V : Set ℝ} (hV : V ∈ 𝓝 0) :
    ∃ A : OpenPartialHomeomorph ℝ ℝ,
      0 ∈ A.source ∧ A 0 = 0 ∧ A.target ⊆ V ∧
      (∀ t, A.symm t = g t) ∧ StrictMonoOn A A.source ∧
      ContDiffOn ℝ ∞ A A.source ∧ ContDiffOn ℝ ∞ A.symm A.target := by
  have hg0 := hg.self_of_nhds
  have hdcont : ContinuousAt (deriv g) 0 :=
    (hg0.derivWithin (m := 0) (by simp)).continuousAt
  have hdpos : ∀ᶠ t in 𝓝 0, 0 < deriv g t :=
    continuousAt_const.eventually_lt hdcont hpos
  obtain ⟨l, r, hzero, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((show ∀ᶠ t in 𝓝 0, t ∈ V from hV).and (hg.and hdpos))
  let W := Ioo l r
  have hWg (t : ℝ) (ht : t ∈ W) : ContDiffAt ℝ ∞ g t := (hsub ht).2.1
  have hWp (t : ℝ) (ht : t ∈ W) : 0 < deriv g t := (hsub ht).2.2
  have hWcont : ContinuousOn g W := fun t ht => (hWg t ht).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn g W :=
    strictMonoOn_of_deriv_pos (convex_Ioo _ _) hWcont
      (fun t ht => hWp t (interior_subset ht))
  have hopenmap : IsOpenMap (W.domRestrict g) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro t
    have hd := ((hWg t t.property).hasStrictDerivAt (by simp)).hasStrictFDerivAt_equiv
      (ne_of_gt (hWp t t.property))
    change 𝓝 (g t) ≤ Filter.map (g ∘ Subtype.val) (𝓝 t)
    rw [← Filter.map_map, isOpen_Ioo.isOpenEmbedding_subtypeVal.map_nhds_eq,
      hd.map_nhds_eq_of_equiv]
  let G := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hmono.injOn.toPartialEquiv g W) hWcont hopenmap isOpen_Ioo
  have hGfun (t : ℝ) : G t = g t := rfl
  have hG0 : 0 ∈ G.source := hzero
  have hGt0 : 0 ∈ G.target := by simpa only [hGfun, hgzero] using G.map_source hG0
  have hGinv0 : G.symm 0 = 0 := by simpa only [hGfun, hgzero] using G.left_inv hG0
  have hGmono : StrictMonoOn G G.source := hmono
  refine ⟨G.symm, hGt0, hGinv0, (fun t ht => (hsub ht).1),
    (fun _ => rfl), ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    by_contra h
    have hle := hGmono.monotoneOn (G.map_target hy) (G.map_target hx) (le_of_not_gt h)
    rw [G.right_inv hy, G.right_inv hx] at hle
    exact (not_le_of_gt hxy) hle
  · intro x hx
    have ht := G.map_target hx
    have hd := ((hWg (G.symm x) ht).hasStrictDerivAt (by simp)).hasStrictFDerivAt_equiv
      (ne_of_gt (hWp (G.symm x) ht))
    exact (G.contDiffAt_symm hx hd.hasFDerivAt (hWg (G.symm x) ht)).contDiffWithinAt
  · intro t ht
    exact (hWg t ht).contDiffWithinAt

theorem exists_axis_of_regular_germ
    {f : ℝ → ℝ × ℝ} (hf : DifferentiableAt ℝ f 0) (hfzero : f 0 = 0)
    (hreg : deriv f 0 ≠ 0)
    (haxes : ∀ᶠ t in 𝓝 0, (f t).1 = 0 ∨ (f t).2 = 0) :
    ∃ horizontal : Bool,
      deriv (fun t => axisCoordinate horizontal (f t)) 0 ≠ 0 ∧
      ∀ᶠ t in 𝓝 0,
        f t = signedAxis horizontal 1 (axisCoordinate horizontal (f t)) := by
  have hcoord (k : Bool) :
      HasDerivAt (fun t => axisCoordinate k (f t)) (axisCoordinate k (deriv f 0)) 0 := by
    cases k
    · simpa [axisCoordinate] using hf.hasDerivAt.hasFDerivAt.snd.hasDerivAt
    · simpa [axisCoordinate] using hf.hasDerivAt.hasFDerivAt.fst.hasDerivAt
  have hex : ∃ k : Bool, axisCoordinate k (deriv f 0) ≠ 0 := by
    by_cases h : (deriv f 0).1 = 0
    · refine ⟨false, ?_⟩
      simpa [axisCoordinate] using (show (deriv f 0).2 ≠ 0 from fun h' =>
        hreg (Prod.ext h h'))
    · exact ⟨true, h⟩
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, ?_, ?_⟩
  · rw [(hcoord k).deriv]
    exact hk
  · have hne : ∀ᶠ t in 𝓝 0, t ≠ 0 → axisCoordinate k (f t) ≠ 0 := by
      simpa using eventually_nhdsWithin_iff.mp ((hcoord k).eventually_ne (c := 0) hk)
    filter_upwards [haxes, hne] with t ht hn
    by_cases htzero : t = 0
    · subst t
      cases k <;> ext <;> simp [hfzero, axisCoordinate, signedAxis]
    have hc := hn htzero
    cases k
    · simp only [axisCoordinate, Bool.false_eq_true, ite_false] at hc
      ext <;> simp [signedAxis, axisCoordinate, ht.resolve_right hc]
    · simp only [axisCoordinate, ite_true] at hc
      ext <;> simp [signedAxis, axisCoordinate, ht.resolve_left hc]

theorem exists_smooth_signed_axis_parametrization
    {f : ℝ → ℝ × ℝ} {U : Set ℝ} (hU : IsOpen U) (hzero : (0 : ℝ) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hfzero : f 0 = 0) (hreg : deriv f 0 ≠ 0)
    (haxes : ∀ᶠ t in 𝓝 0, (f t).1 = 0 ∨ (f t).2 = 0) :
    ∃ (horizontal : Bool) (sign δ : ℝ) (A : OpenPartialHomeomorph ℝ ℝ),
      (sign = 1 ∨ sign = -1) ∧ 0 < δ ∧ A 0 = 0 ∧
      Icc 0 δ ⊆ A.source ∧ A.target ⊆ U ∧ StrictMonoOn A A.source ∧
      ContDiffOn ℝ ∞ A A.source ∧ ContDiffOn ℝ ∞ A.symm A.target ∧
      (∀ t, A.symm t = sign * axisCoordinate horizontal (f t)) ∧
      (∀ u ∈ A.source, f (A u) = signedAxis horizontal sign u) ∧
      (∀ u ∈ Ioc 0 δ, 0 < A u ∧
        A '' Icc 0 u = Icc 0 (A u) ∧
        f '' Icc 0 (A u) = signedAxis horizontal sign '' Icc 0 u) := by
  have hf0 := hf.contDiffAt (hU.mem_nhds hzero)
  obtain ⟨k, hk, haxis⟩ := exists_axis_of_regular_germ
    (hf0.differentiableAt (by simp)) hfzero hreg haxes
  let g : ℝ → ℝ := fun t => axisCoordinate k (f t)
  have hg (t : ℝ) (ht : t ∈ U) : ContDiffAt ℝ ∞ g t := by
    cases k
    · exact (hf.contDiffAt (hU.mem_nhds ht)).snd
    · exact (hf.contDiffAt (hU.mem_nhds ht)).fst
  obtain ⟨sign, hsign, hpos⟩ : ∃ sign : ℝ,
      (sign = 1 ∨ sign = -1) ∧ 0 < sign * deriv g 0 := by
    rcases lt_or_gt_of_ne hk with hneg | hpos
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by simpa using hpos⟩
  have hsignsq : sign * sign = 1 := by rcases hsign with rfl | rfl <;> norm_num
  let q : ℝ → ℝ := fun t => sign * g t
  have hqsmooth : ∀ᶠ t in 𝓝 0, ContDiffAt ℝ ∞ q t := by
    filter_upwards [hU.mem_nhds hzero] with t ht
    exact contDiffAt_const.mul (hg t ht)
  have hqzero : q 0 = 0 := by cases k <;> simp [q, g, axisCoordinate, hfzero]
  have hqpos : 0 < deriv q 0 := by
    have hd := ((hg 0 hzero).differentiableAt (by simp)).hasDerivAt.const_mul sign
    rw [hd.deriv]
    exact hpos
  obtain ⟨A, hA0, hAzero, hAtarget, hAinv, hAmono, hAsmooth, hAinvsmooth⟩ :=
    exists_smooth_increasing_inverse hqsmooth hqzero hqpos
      ((show ∀ᶠ t in 𝓝 0, t ∈ U from hU.mem_nhds hzero).and haxis)
  have hAaxis (u : ℝ) (hu : u ∈ A.source) :
      f (A u) = signedAxis k sign u := by
    have ht := hAtarget (A.map_source hu)
    have hq : sign * g (A u) = u := by simpa only [hAinv] using A.left_inv hu
    have hgval : g (A u) = sign * u := by
      calc
        g (A u) = (sign * sign) * g (A u) := by rw [hsignsq, one_mul]
        _ = sign * u := by rw [mul_assoc, hq]
    rw [ht.2]
    change signedAxis k 1 (g (A u)) = signedAxis k sign u
    rw [hgval]
    cases k <;> simp [signedAxis]
  obtain ⟨l, r, h0, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (A.open_source.mem_nhds hA0)
  let δ := r / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith [h0.2]
  have hδsub : Icc 0 δ ⊆ A.source := by
    intro u hu
    exact hsub ⟨h0.1.trans_le hu.1, by dsimp [δ] at hu; linarith [hu.2, h0.2]⟩
  refine ⟨k, sign, δ, A, hsign, hδ, hAzero, hδsub,
    (fun t ht => (hAtarget ht).1), hAmono, hAsmooth, hAinvsmooth,
    hAinv, hAaxis, ?_⟩
  intro u hu
  have husub : Icc 0 u ⊆ A.source := (Icc_subset_Icc_right hu.2).trans hδsub
  have huA : u ∈ A.source := husub (right_mem_Icc.mpr hu.1.le)
  have hAu : 0 < A u := by simpa only [hAzero] using hAmono hA0 huA hu.1
  have himage : A '' Icc 0 u = Icc 0 (A u) := by
    simpa only [hAzero] using (A.continuousOn.mono husub).image_Icc_of_monotoneOn
      hu.1.le (hAmono.monotoneOn.mono husub)
  refine ⟨hAu, himage, ?_⟩
  rw [← himage, image_image]
  exact image_congr (fun t ht => hAaxis t (husub ht))

end Poincare.Topology.Plane.Curves
