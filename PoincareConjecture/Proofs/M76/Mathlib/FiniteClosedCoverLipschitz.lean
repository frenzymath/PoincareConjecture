import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Affine.AddTorsor

set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

theorem dist_endpoints_le_of_local_right_bound {F : Type*} [PseudoMetricSpace F]
    {f : ℝ → F} {a b C : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hlocal : ∀ x ∈ Ico a b, ∀ᶠ y in 𝓝[>] x, dist (f y) (f x) ≤ C * (y - x)) :
    dist (f b) (f a) ≤ C * (b - a) := by
  have hB (x : ℝ) : HasDerivAt (fun t : ℝ => C * (t - a)) C x := by
    simpa using ((hasDerivAt_id x).sub_const a).const_mul C
  apply image_le_of_liminf_slope_right_le_deriv_boundary
    (continuous_dist.comp_continuousOn (hf.prodMk continuousOn_const)) (by simp) (by fun_prop)
    (fun x _ => (hB x).hasDerivWithinAt) ?_ ⟨hab, le_rfl⟩
  intro x hx r hr
  apply Filter.Eventually.frequently
  filter_upwards [hlocal x hx, self_mem_nhdsWithin] with y hy hyx
  have hpos : 0 < y - x := sub_pos.mpr hyx
  have htri := dist_triangle (f y) (f x) (f a)
  rw [slope_def_field]
  apply lt_of_le_of_lt ((div_le_iff₀ hpos).mpr ?_) hr
  change dist (f y) (f a) - dist (f x) (f a) ≤ C * (y - x)
  linarith

theorem Convex.lipschitzOnWith_of_local_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace F]
    {s : Set E} {f : E → F} {K : ℝ≥0} (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hlocal : ∀ x ∈ s, ∀ᶠ y in 𝓝[s] x, dist (f y) (f x) ≤ K * dist y x) :
    LipschitzOnWith K f s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  let a : ℝ → E := AffineMap.lineMap y x
  have hac : Continuous a := (lipschitzWith_lineMap y x).continuous
  have ham : MapsTo a (Icc (0 : ℝ) 1) s := hs.mapsTo_lineMap hy hx
  have hfac : ContinuousOn (f ∘ a) (Icc (0 : ℝ) 1) :=
    hf.comp hac.continuousOn ham
  have hb := dist_endpoints_le_of_local_right_bound zero_le_one hfac
    (C := (K : ℝ) * dist x y) (fun t ht => ?_)
  · simpa [a] using hb
  have htm : a t ∈ s := ham (Ico_subset_Icc_self ht)
  have hev := (hac.continuousWithinAt.tendsto_nhdsWithin ham) (hlocal (a t) htm)
  have hev' : ∀ᶠ z in 𝓝[>] t, dist (f (a z)) (f (a t)) ≤ K * dist (a z) (a t) :=
    nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ht) hev
  filter_upwards [hev', self_mem_nhdsWithin] with z hz hzt
  change dist (f (a z)) (f (a t)) ≤ (K : ℝ) * dist x y * (z - t)
  have hd : dist (a z) (a t) = (z - t) * dist x y := by
    rw [show a = AffineMap.lineMap y x from rfl, dist_lineMap_lineMap,
      Real.dist_eq, abs_of_pos (sub_pos.mpr hzt), dist_comm y x]
  calc
    _ ≤ (K : ℝ) * dist (a z) (a t) := hz
    _ = _ := by rw [hd]; ring

theorem Convex.lipschitzOnWith_of_finite_closed_cover {E F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace F] [Finite ι]
    {s : Set E} {f : E → F} {K : ℝ≥0} (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (u : ι → Set E) (hu : ∀ i, IsClosed (u i)) (hcover : s ⊆ ⋃ i, u i)
    (hbound : ∀ i, LipschitzOnWith K f (s ∩ u i)) : LipschitzOnWith K f s := by
  apply hs.lipschitzOnWith_of_local_bound hf
  intro x hx
  have hall : ∀ᶠ y in 𝓝 x, ∀ i, y ∈ u i → x ∈ u i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hxi : x ∈ u i
    · exact Filter.Eventually.of_forall fun _ _ => hxi
    · have he : ∀ᶠ y in 𝓝 x, y ∉ u i := (hu i).isOpen_compl.mem_nhds hxi
      exact he.mono fun _ hy hyi => (hy hyi).elim
  have hall' : ∀ᶠ y in 𝓝[s] x, ∀ i, y ∈ u i → x ∈ u i := nhdsWithin_le_nhds hall
  filter_upwards [hall', self_mem_nhdsWithin] with y hy hys
  obtain ⟨i, hyi⟩ := mem_iUnion.mp (hcover hys)
  exact (hbound i).dist_le_mul y ⟨hys, hyi⟩ x ⟨hx, hy i hyi⟩
