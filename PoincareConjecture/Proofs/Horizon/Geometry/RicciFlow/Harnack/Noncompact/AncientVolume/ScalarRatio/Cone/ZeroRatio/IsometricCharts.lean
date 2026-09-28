import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.NormalBall
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.MetricArc
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.LocalQuadratic













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_smooth_squared_distance_neighborhood (g : RiemannianMetric n M) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => (g.edist p x).toReal ^ 2 / 2) U := by
  let E := EuclideanSpace ℝ (Fin n)
  obtain ⟨e, h0, he0, he, he', hgauss, _, _⟩ := g.exists_exponential_chart_gauss p
  obtain ⟨r, hr, hsource, hdist⟩ :=
    g.exists_tangentBall_edist_eq_of_gauss p e h0 he0 he he' hgauss
  let T : Set E := {v | g.tangentNorm p v < r}
  have hT : IsOpen T := by
    apply isOpen_lt _ continuous_const
    unfold tangentNorm
    exact Real.continuous_sqrt.comp
      ((continuous_const.clm_apply continuous_id).clm_apply continuous_id)
  let U : Set M := e '' T
  have hU : IsOpen U := e.isOpen_image_of_subset_source hT hsource
  have hpU : p ∈ U := ⟨0, by
    change g.tangentNorm p 0 < r
    simpa [tangentNorm] using hr, he0⟩
  have hUt : U ⊆ e.target := fun x ⟨v, hv, hvx⟩ => hvx ▸ e.map_source (hsource hv)
  let Q : E → ℝ := fun v => g.inner p v v / 2
  have hQ : ContDiff ℝ ∞ Q := by
    let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p
    change ContDiff ℝ ∞ (fun v => B v v / 2)
    fun_prop
  have hformula : EqOn (fun x => (g.edist p x).toReal ^ 2 / 2) (Q ∘ e.symm) U := by
    rintro x ⟨v, hv, rfl⟩
    change (g.edist p (e v)).toReal ^ 2 / 2 = Q (e.symm (e v))
    rw [hdist v hv, tangentNorm, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    have hvpos : 0 ≤ g.inner p v v := by
      by_cases h : v = 0
      · simp [h]
      · exact (g.pos p v h).le
    simp only [e.left_inv (hsource hv), Q, Real.sq_sqrt hvpos]
  exact ⟨U, hU, hpU, ((contMDiff_iff_contDiff.mpr hQ).comp_contMDiffOn
    (he'.mono hUt)).congr hformula⟩



theorem contMDiffAt_squared_distance_self (g : RiemannianMetric n M) (p : M) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => (g.edist p x).toReal ^ 2 / 2) p := by
  obtain ⟨U, hU, hpU, hsmooth⟩ := g.exists_smooth_squared_distance_neighborhood p
  exact hsmooth.contMDiffAt (hU.mem_nhds hpU)




theorem IsGeodesicOn.comp_of_edist_eq
    [T3Space M] [PreconnectedSpace M]
    {m : ℕ} {N : Type*} [TopologicalSpace N] [T2Space N]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N] [IsManifold (𝓡 m) ∞ N]
    {g : RiemannianMetric n M} (h : RiemannianMetric m N)
    {f : M → N} {U : Set M}
    (hf : ∀ x ∈ U, ∀ y ∈ U, h.edist (f x) (f y) = g.edist x y)
    {γ : ℝ → M} {J : Set ℝ} (hγ : g.IsGeodesicOn γ J)
    (hJ : IsOpen J) (hγU : MapsTo γ J U) :
    h.IsGeodesicOn (f ∘ γ) J ∧ ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 m) ∞ (f ∘ γ) J := by
  have hpoint (t₀ : ℝ) (ht₀ : t₀ ∈ J) :
      h.IsGeodesicOn (f ∘ γ) {t₀} ∧ ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 m) ∞ (f ∘ γ) t₀ := by
    obtain ⟨δ, hδ, hsub, _, hmin⟩ := hγ.exists_minimizing_affine_neighborhood hJ ht₀
    let a := t₀ - δ
    let b := t₀ + δ
    let η := fun u => γ (2 * δ * u + a)
    let d := g.edist (η 0) (η 1)
    have hd : d ≠ ⊤ := g.edist_ne_top _ _
    have htime (s : ℝ) (hs : s ∈ Ioo a b) : (s - a) / (2 * δ) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hs.1.le) (by positivity)
      · apply (div_le_one (by positivity : 0 < 2 * δ)).mpr
        dsimp [a, b] at hs ⊢
        linarith [hs.2]
    have hback (s : ℝ) : η ((s - a) / (2 * δ)) = γ s := by
      dsimp [η]
      congr 1
      field_simp
      ring
    have hJsmall : Ioo a b ⊆ J := by
      intro s hs
      apply hsub
      dsimp [a, b] at hs
      constructor <;> linarith [hs.1, hs.2]
    obtain ⟨hgeo, hsmooth⟩ := h.isGeodesicOn_and_contMDiffOn_of_edist_affine_segment
      (γ := f ∘ γ) (a := a) (b := b) (c := d.toReal / (2 * δ))
      (by positivity) (by
        intro s hs t ht
        change h.edist (f (γ s)) (f (γ t)) = _
        rw [hf _ (hγU (hJsmall hs)) _ (hγU (hJsmall ht))]
        have hh := hmin ((s - a) / (2 * δ)) (htime s hs)
          ((t - a) / (2 * δ)) (htime t ht)
        change g.edist (η ((s - a) / (2 * δ))) (η ((t - a) / (2 * δ))) =
          ENNReal.ofReal |(s - a) / (2 * δ) - (t - a) / (2 * δ)| * d at hh
        rw [hback, hback] at hh
        rw [hh, ← ENNReal.ofReal_toReal hd, ← ENNReal.ofReal_mul (abs_nonneg _),
          ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
        congr 1
        rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos (by positivity : 0 < 2 * δ)]
        ring)
    have ht : t₀ ∈ Ioo a b := by dsimp [a, b]; constructor <;> linarith
    exact ⟨(fun s hs => by have hs' : s = t₀ := hs; subst s; exact hgeo t₀ ht),
      hsmooth.contMDiffAt (isOpen_Ioo.mem_nhds ht)⟩
  exact ⟨fun t ht => (hpoint t ht).1 t rfl,
    fun t ht => (hpoint t ht).2.contMDiffWithinAt⟩

end PoincareConjecture.RiemannianMetric
