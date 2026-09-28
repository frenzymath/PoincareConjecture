import PoincareConjecture.Proofs.M14.Sec6_4_GaugeVelocity
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift
import PoincareConjecture.Proofs.M14.Sec6_2_VariationClock

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p} (V : M14LVariationData G p R)

theorem exists_variation_gauge_rectangle {s : ℝ}
    (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    ∃ (b : G.gaugeCover.index) (N P : Set ℝ)
      (β : ℝ × ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
        G.gaugeCover.spatial b),
      IsOpen N ∧ s ∈ N ∧ IsOpen P ∧ (0 : ℝ) ∈ P ∧ P ⊆ V.parameterDomain ∧
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β
        ((M14SqrtParameterInterval τ₁ τ₂ ∩ N) ×ˢ P) ∧
      (∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N, ∀ u ∈ P,
        (G.gaugeCover.cylinder b).toSpacetime (β (r, u)) = V.squareFamily r u) ∧
      (∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N, ∀ u ∈ P,
        (β (r, u)).1.val = T - r ^ 2) := by
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  obtain ⟨b, O, lift, hO, hbase, hlift, hright, hclock⟩ :=
    exists_smooth_gauge_lift G (V.squareFamily s 0)
  let α : ℝ × ℝ → G.Point := fun z => V.squareFamily z.1 z.2
  have hα := V.square_smooth.mono V.square_contains
  have hpre : α ⁻¹' O ∈ 𝓝[M14SqrtParameterInterval τ₁ τ₂ ×ˢ V.parameterDomain] (s, 0) :=
    (hα.continuousOn (s, 0) ⟨hs, hzero⟩).preimage_mem_nhdsWithin (hO.mem_nhds hbase)
  obtain ⟨A, hA, hAsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
  obtain ⟨N, Q, hN, hsN, hQ, hzeroQ, hprod⟩ := mem_nhds_prod_iff'.mp hA
  let P := Q ∩ V.parameterDomain
  have hmap : MapsTo α ((M14SqrtParameterInterval τ₁ τ₂ ∩ N) ×ˢ P) O := by
    intro z hz
    exact hAsub ⟨hprod ⟨hz.1.2, hz.2.1⟩, ⟨hz.1.1, hz.2.2⟩⟩
  have hsub : ((M14SqrtParameterInterval τ₁ τ₂ ∩ N) ×ˢ P) ⊆
      M14SqrtParameterInterval τ₁ τ₂ ×ˢ V.parameterDomain :=
    fun _ hz => ⟨hz.1.1, hz.2.2⟩
  refine ⟨b, N, P, fun z => lift (α z), hN, hsN, hQ.inter hP,
    ⟨hzeroQ, hzero⟩, inter_subset_right, hlift.comp (hα.mono hsub) hmap, ?_, ?_⟩
  · intro r hr u hu
    exact hright _ (hmap ⟨hr, hu⟩)
  · intro r hr u hu
    exact (hclock _ (hmap ⟨hr, hu⟩)).trans (variation_squareFamily_time V hr.1 hu.2)

variable (b : G.gaugeCover.index)
  {β : ℝ × ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b}

theorem variationGauge_spatial_contDiffOn {S P : Set ℝ}
    (hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β (S ×ˢ P)) :
    ContDiffOn ℝ ∞ (fun z => (β z).2.val) (S ×ˢ P) := by
  have hval : ContMDiff (𝓡 n) (𝓡 n) ∞
      (Subtype.val : G.gaugeCover.spatial b → EuclideanSpace ℝ (Fin n)) :=
    contMDiff_subtype_val
  have hsp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) ∞
      (fun z => (β z).2) (S ×ˢ P) := fun z hz => (hβ z hz).snd
  have h := hval.comp_contMDiffOn hsp
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffOn

theorem endpointVariationField_gauge {S P : Set ℝ} (hP : IsOpen P)
    (hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β (S ×ˢ P))
    (hrec : ∀ r ∈ S, ∀ u ∈ P,
      (G.gaugeCover.cylinder b).toSpacetime (β (r, u)) = V.squareFamily r u)
    {s u : ℝ} (hs : s ∈ S) (hu : u ∈ P) :
    HEq (M14EndpointVariationField V s u)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β (s, u)).1 (β (s, u)).2
        (deriv (fun r => (β (s, r)).2.val) u)) := by
  have hcurve := hβ.comp ((contMDiff_const (c := s)).prodMk contMDiff_id).contMDiffOn
    (fun _ hr => ⟨hs, hr⟩)
  have hproj := gaugeCurve_projectedVelocityWithin b
    ((hcurve u hu).mdifferentiableWithinAt (by simp)) (hP.uniqueDiffOn u hu)
  have hcongr := projectedCurveVelocityWithin_congrOn
    (G := G) (J := P) (fun r hr => (hrec s hs r hr).symm) hu
  have h := hcongr.trans (heq_of_eq hproj)
  dsimp only [Function.comp_def, id_eq] at h
  have hd := congrArg (fun v : EuclideanSpace ℝ (Fin n) =>
    (G.gaugeCover.metric b).spatialTangentEquiv (β (s, u)).1 (β (s, u)).2 v)
    (derivWithin_of_mem_nhds (f := fun r => (β (s, r)).2.val) (hP.mem_nhds hu))
  simpa only [projectedCurveVelocityWithin, M14EndpointVariationField,
    mfderivWithin_of_mem_nhds (hP.mem_nhds hu)] using h.trans (heq_of_eq hd)

theorem variationSquareVelocity_gauge {N P : Set ℝ} (hN : IsOpen N)
    (hβ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞ β
      ((M14SqrtParameterInterval τ₁ τ₂ ∩ N) ×ˢ P))
    (hrec : ∀ r ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N, ∀ u ∈ P,
      (G.gaugeCover.cylinder b).toSpacetime (β (r, u)) = V.squareFamily r u)
    {s u : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂ ∩ N) (hu : u ∈ P) :
    HEq (variationSquareVelocity V s u)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β (s, u)).1 (β (s, u)).2
        (derivWithin (fun r => (β (r, u)).2.val)
          (M14SqrtParameterInterval τ₁ τ₂ ∩ N) s)) := by
  have hcurve := hβ.comp (contMDiff_id.prodMk (contMDiff_const (c := u))).contMDiffOn
    (fun _ hr => ⟨hr, hu⟩)
  have hJ := (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)).inter hN
  have hproj := gaugeCurve_projectedVelocityWithin b
    ((hcurve s hs).mdifferentiableWithinAt (by simp)) (hJ s hs)
  have hcongr := projectedCurveVelocityWithin_congrOn (G := G)
    (J := M14SqrtParameterInterval τ₁ τ₂ ∩ N) (fun r hr => (hrec r hr u hu).symm) hs
  have h := hcongr.trans (heq_of_eq hproj)
  dsimp only [Function.comp_def, id_eq] at h
  simpa only [projectedCurveVelocityWithin, variationSquareVelocity,
    mfderivWithin_inter (hN.mem_nhds hs.2)] using h

end PoincareConjecture.M14
