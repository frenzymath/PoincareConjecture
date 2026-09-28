import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckSphereProjection
import Mathlib.Geometry.Manifold.Algebra.Structures

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

private abbrev CI := (𝓡 2).prod 𝓘(ℝ, ℝ)
private abbrev SE := EuclideanSpace ℝ (Fin 2)
private abbrev CE := EuclideanSpace ℝ (Fin 3)

private def neckGraphShear (f : UnitTwoSphere → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) : RoundCylinderSpace ≃ₜ RoundCylinderSpace where
  toFun z := (z.1, z.2 - f z.1)
  invFun z := (z.1, z.2 + f z.1)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_fst.prodMk
    (continuous_snd.sub (hf.continuous.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk
    (continuous_snd.add (hf.continuous.comp continuous_fst))

private theorem contMDiff_neckGraphShear (f : UnitTwoSphere → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff CI CI ∞ (neckGraphShear f hf) :=
  contMDiff_fst.prodMk (contMDiff_snd.sub (hf.comp contMDiff_fst))

private theorem contMDiff_neckGraphShear_symm (f : UnitTwoSphere → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff CI CI ∞ (neckGraphShear f hf).symm :=
  contMDiff_fst.prodMk (contMDiff_snd.add (hf.comp contMDiff_fst))

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace CE M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private def neckGraphChart (N : EpsilonNeck g) (f : UnitTwoSphere → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f) (p : UnitTwoSphere) :
    OpenPartialHomeomorph M CE :=
  (((N.coordinatePartialHomeomorph.symm.trans
    (neckGraphShear f hf).toOpenPartialHomeomorph).trans
    ((chartAt SE p).prod (OpenPartialHomeomorph.refl ℝ))).trans
    (RiemannianMetric.lineModelEquiv 2).toHomeomorph.toOpenPartialHomeomorph)

private theorem neckGraphChart_mem_maximalAtlas (N : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (p : UnitTwoSphere) :
    neckGraphChart N f hf p ∈ IsManifold.maximalAtlas (𝓡 3) ∞ M := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · apply (RiemannianMetric.lineModelEquiv 2).contDiff.contMDiff.comp_contMDiffOn
    apply ContMDiffOn.prodMk_space
    · apply (contMDiffOn_chart (I := 𝓡 2) (x := p)).comp
      · exact contMDiff_fst.comp_contMDiffOn
          ((contMDiff_neckGraphShear f hf).comp_contMDiffOn
            (N.coordinate_inverse_smooth.mono (fun x hx => hx.1.1.1)))
      · intro x hx
        exact hx.1.2.1
    · exact contMDiff_snd.comp_contMDiffOn
        ((contMDiff_neckGraphShear f hf).comp_contMDiffOn
          (N.coordinate_inverse_smooth.mono (fun x hx => hx.1.1.1)))
  · apply N.coordinate_map_smooth.comp
    · apply (contMDiff_neckGraphShear_symm f hf).comp_contMDiffOn
      apply ContMDiffOn.prodMk
      · apply (contMDiffOn_chart_symm (I := 𝓡 2) (x := p)).comp
        · exact (contDiff_fst.comp
            (RiemannianMetric.lineModelEquiv 2).symm.contDiff).contMDiff.contMDiffOn
        · intro z hz
          exact hz.2.1.1
      · exact (contDiff_snd.comp
          (RiemannianMetric.lineModelEquiv 2).symm.contDiff).contMDiff.contMDiffOn
    · intro z hz
      exact hz.2.2.2

private theorem neck_graph_contMDiff (N : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hdom : ∀ p, f p ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiff (𝓡 2) (𝓡 3) ∞ (fun p : UnitTwoSphere => N.coordinate_map (p, f p)) :=
  N.coordinate_map_smooth.comp_contMDiff (contMDiff_id.prodMk hf)
    (fun p => ⟨mem_univ _, hdom p⟩)

private theorem neck_graph_isImmersion (N : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hdom : ∀ p, f p ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    Manifold.IsImmersion (𝓡 2) (𝓡 3) ∞
      (fun p : UnitTwoSphere => N.coordinate_map (p, f p)) := by
  apply Manifold.IsImmersionOfComplement.isImmersion (F := ℝ)
  intro p
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (neck_graph_contMDiff N f hf hdom).continuous.continuousAt
    (RiemannianMetric.lineModelEquiv 2)
    (chartAt SE p) (neckGraphChart N f hf p)
    (mem_chart_source _ p) ?_ (IsManifold.chart_mem_maximalAtlas p)
    (neckGraphChart_mem_maximalAtlas N f hf p) ?_
  · change (((N.coordinate_map (p, f p) ∈ N.carrier ∧
      N.coordinate_inverse (N.coordinate_map (p, f p)) ∈ univ) ∧
      (neckGraphShear f hf) (N.coordinate_inverse (N.coordinate_map (p, f p))) ∈
        (chartAt SE p).source ×ˢ univ) ∧ _)
    refine ⟨⟨⟨N.coordinate_map_mem ⟨mem_univ _, hdom p⟩, mem_univ _⟩,
      ?_⟩, mem_univ _⟩
    rw [N.coordinate_inverse_coordinate_map ⟨mem_univ _, hdom p⟩]
    exact ⟨mem_chart_source _ p, mem_univ _⟩
  · intro y hy
    have hy' : y ∈ (chartAt SE p).target := hy.2
    change RiemannianMetric.lineModelEquiv 2
      (((chartAt SE p)
        ((neckGraphShear f hf) (N.coordinate_inverse (N.coordinate_map
          ((chartAt SE p).symm y, f ((chartAt SE p).symm y))))).1),
        ((neckGraphShear f hf) (N.coordinate_inverse (N.coordinate_map
          ((chartAt SE p).symm y, f ((chartAt SE p).symm y))))).2) = _
    rw [N.coordinate_inverse_coordinate_map ⟨mem_univ _, hdom _⟩]
    change RiemannianMetric.lineModelEquiv 2
      ((chartAt SE p) ((chartAt SE p).symm y),
        f ((chartAt SE p).symm y) - f ((chartAt SE p).symm y)) =
      RiemannianMetric.lineModelEquiv 2 (y, 0)
    rw [(chartAt SE p).right_inv hy', sub_self]

theorem neck_graph_isSmoothEmbedding [T2Space M] (N : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hdom : ∀ p, f p ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
      (fun p : UnitTwoSphere => N.coordinate_map (p, f p)) := by
  have hinj : Function.Injective (fun p : UnitTwoSphere => N.coordinate_map (p, f p)) := by
    intro p q hpq
    have h := congrArg (fun x => (N.coordinate_inverse x).1) hpq
    rw [N.coordinate_inverse_coordinate_map ⟨mem_univ _, hdom p⟩,
      N.coordinate_inverse_coordinate_map ⟨mem_univ _, hdom q⟩] at h
    exact h
  exact ⟨neck_graph_isImmersion N f hf hdom,
    ((neck_graph_contMDiff N f hf hdom).continuous.isClosedEmbedding hinj).isEmbedding⟩

theorem neck_graph_isotopic_central [T2Space M] (N : EpsilonNeck g)
    (f : UnitTwoSphere → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hdom : ∀ p, f p ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    SmoothSphereIsotopicIn N.carrier
      (range (fun p : UnitTwoSphere => N.coordinate_map (p, f p))) N.central_sphere := by
  let height : ℝ × UnitTwoSphere → ℝ := fun z => (1 - z.1) * f z.2
  have hsmooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ height :=
    (contMDiff_const.sub contMDiff_fst).mul (hf.comp contMDiff_snd)
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hheight (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (p : UnitTwoSphere) :
      height (t, p) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    have h := convex_Ioo _ _ (hdom p) hzero (sub_nonneg.mpr ht.2) ht.1
      (show (1 - t) + t = 1 by ring)
    simpa only [height, smul_eq_mul, mul_zero, add_zero] using h
  refine ⟨fun z => N.coordinate_map (z.2, height z), ?_, ?_, ?_, ?_⟩
  · exact N.coordinate_map_smooth.comp
      (contMDiff_snd.prodMk hsmooth).contMDiffOn
      (fun z hz => ⟨mem_univ _, hheight z.1 hz.1 z.2⟩)
  · intro t ht
    have hs : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun p => height (t, p)) := by
      have hproduct : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
          ((fun _ : UnitTwoSphere => (1 - t : ℝ)) * f) :=
        (contMDiff_const (c := (1 - t : ℝ))).mul hf
      have heq : ((fun _ : UnitTwoSphere => (1 - t : ℝ)) * f) =
          (fun p => height (t, p)) := by
        funext p
        rfl
      rw [← heq]
      exact hproduct
    refine ⟨neck_graph_isSmoothEmbedding N (fun p => height (t, p))
      hs (hheight t ht), ?_⟩
    rintro x ⟨p, rfl⟩
    exact N.coordinate_map_mem ⟨mem_univ _, hheight t ht p⟩
  · simp only [height, sub_zero, one_mul]
  · simpa only [height, sub_self, zero_mul] using N.centralSphere_range

theorem exists_buffered_neck_sphere_isotopy_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (_D : LeviCivitaData g)
        (N N' : EpsilonNeck g),
        N.epsilon ≤ epsilon₀ → N'.epsilon ≤ epsilon₀ →
        ∀ a ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹, ∀ q : UnitTwoSphere,
          N'.coordinate_map (q, a) ∈ N.carrier →
          |(N.coordinate_inverse (N'.coordinate_map (q, a))).2| ≤
            3 * N.epsilon⁻¹ / 4 →
          SmoothSphereIsotopicIn N.carrier
            (range (fun p : UnitTwoSphere => N'.coordinate_map (p, a)))
            N.central_sphere := by
  obtain ⟨epsilon₀, hpos, hsmall, hgraph⟩ := exists_buffered_neck_sphere_graph_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g D N N' hN hN' a ha q hy haxis
  obtain ⟨_, _, f, hf, hbuffer, _, hrange⟩ := hgraph M g D N N' hN hN' a ha q hy haxis
  have hdom (p : UnitTwoSphere) : f p ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    have h := abs_lt.mp (hbuffer p)
    have hpos := inv_pos.mpr N.epsilon_pos
    constructor <;> linarith [h.1, h.2]
  rw [hrange]
  exact neck_graph_isotopic_central N f hf hdom

end PoincareConjecture.M28
