import PoincareConjecture.Proofs.M76.Wall.Mathlib.CompatibleChartFormula
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompatibleInverseChart
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactClosedStrip

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (-1 : ℝ) 1

theorem OriginalSurfacePairChart.exists_transverse_patch
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {S T : Set X} {y : X}
    (B : OriginalSurfacePairChart e S T y true)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {p : E → X} (hp : PolyhedralPLInCharts e p K.space) (hpi : InjOn p K.space)
    (hps : MapsTo p K.space B.chart.source)
    (hpc : MapsTo (B.chart ∘ p) K.space B.coordinates.source)
    (hpS : MapsTo p K.space S) :
    ∃ (δ : ℝ) (F : E × ℝ → X), 0 < δ ∧ δ ≤ 1 / 2 ∧
      PolyhedralPLInCharts e F (K.space ×ˢ I) ∧ InjOn F (K.space ×ˢ I) ∧
      MapsTo F (K.space ×ˢ I) B.chart.source ∧
      MapsTo (B.chart ∘ F) (K.space ×ˢ I) B.coordinates.source ∧
      (∀ x ∈ K.space, F (x, 0) = p x) ∧
      (∀ z ∈ K.space ×ˢ I,
        B.coordinates (B.chart (F z)) = ((B.coordinates (B.chart (p z.1))).1, δ * z.2)) ∧
      (∀ z ∈ K.space ×ˢ I, F z ∈ S ↔ z.2 = 0) ∧
      ∀ z ∈ K.space ×ˢ I, F z ∈ T ↔ p z.1 ∈ T := by
  let q : E → C3 := B.coordinates ∘ B.chart ∘ p
  have hq : FinitePiecewiseAffineOn q K.space :=
    B.forwardPL.comp_finitePiecewiseAffineOn
      (hp.finitePiecewiseAffineOn_compatible_chart B.chart B.compatible K hK subset_rfl hps) hpc
  have hqtarget : MapsTo q K.space B.coordinates.target :=
    fun x hx => B.coordinates.map_source (hpc hx)
  have hfirst (x : E) (hx : x ∈ K.space) : (q x).2 = 0 ∧ 0 ≤ (q x).1.2 := by
    have h := (B.first_surface (B.chart (p x)) (hpc hx)).mp
      ((B.chart.left_inv (hps hx)).symm ▸ hpS hx)
    exact ⟨h.1, h.2 rfl⟩
  have hqi : InjOn q K.space := by
    intro x hx z hz heq
    exact hpi hx hz (B.chart.injOn (hps hx) (hps hz)
      (B.coordinates.injOn (hpc hx) (hpc hz) heq))
  let c : K.space × I → C3 := fun z => ((q z.1).1, (z.2 : ℝ))
  have hc : Continuous c :=
    (continuous_fst.comp (hq.continuousOn.domRestrict.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd)
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  have hc0 (x : K.space) : c (x, ⟨0, by norm_num⟩) ∈ B.coordinates.target := by
    have heq : c (x, ⟨0, by norm_num⟩) = q x := Prod.ext rfl (hfirst x x.property).1.symm
    exact heq.symm ▸ hqtarget x.property
  obtain ⟨δ, hδ, hδsmall, hthin⟩ :=
    hc.exists_closed_strip_subset B.coordinates.open_target hc0
  let g : E × ℝ → C3 := fun z => ((q z.1).1, δ * z.2)
  have hgmap : MapsTo g (K.space ×ˢ I) B.coordinates.target := by
    intro z hz
    have habs : |δ * z.2| ≤ δ := by
      rw [abs_mul, abs_of_pos hδ]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr hz.2) hδ.le).trans_eq (mul_one δ)
    have hI : δ * z.2 ∈ I := by
      obtain ⟨hl, hu⟩ := abs_le.mp habs
      exact ⟨by linarith, by linarith⟩
    exact hthin ⟨z.1, hz.1⟩ ⟨δ * z.2, hI⟩ habs
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)
  let scale : ℝ →ᴬ[ℝ] ℝ := δ • ContinuousAffineMap.id ℝ ℝ
  have hscale : FinitePiecewiseAffineOn scale I := ⟨J, hJ, hJI, J.affineOnFaces_affine scale⟩
  have hg : FinitePiecewiseAffineOn g (K.space ×ˢ I) :=
    (hq.postcomp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap).prodMap hscale
  have hgi : InjOn g (K.space ×ˢ I) := by
    intro z hz w hw heq
    have hfirstEq := congrArg Prod.fst heq
    have hlastEq := congrArg Prod.snd heq
    exact Prod.ext (hqi hz.1 hw.1 (Prod.ext hfirstEq
      ((hfirst z.1 hz.1).1.trans (hfirst w.1 hw.1).1.symm)))
      (mul_left_cancel₀ hδ.ne' hlastEq)
  let F : E × ℝ → X := B.chart.symm ∘ B.coordinates.symm ∘ g
  have hsource (z) (hz : z ∈ K.space ×ˢ I) :
      B.coordinates.symm (g z) ∈ B.coordinates.source := B.coordinates.map_target (hgmap hz)
  have hchart (z) (hz : z ∈ K.space ×ˢ I) :
      B.chart (F z) = B.coordinates.symm (g z) :=
    B.chart.right_inv (B.source_subset (hsource z hz))
  have hcoords (z) (hz : z ∈ K.space ×ˢ I) :
      B.coordinates (B.chart (F z)) = g z := by
    rw [hchart z hz, B.coordinates.right_inv (hgmap hz)]
  have hF : PolyhedralPLInCharts e F (K.space ×ˢ I) := by
    have hinv := B.inversePL.comp_finitePiecewiseAffineOn hg hgmap
    obtain ⟨L, hL, hLs, hLa⟩ := hinv
    rw [← hLs]
    exact polyhedralPLInCharts_of_compatible_chart_inverse e hcover B.chart (fun i => by
      simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.symm_symm] using (piecewiseAffineGroupoid V3).symm (B.compatible i))
      L hL ⟨L, hL, rfl, hLa⟩ (fun z hz => B.source_subset (hsource z (hLs.subset hz)))
  refine ⟨δ, F, hδ, hδsmall, hF, ?_, ?_, ?_, ?_, hcoords, ?_, ?_⟩
  · exact B.chart.symm.injOn.comp (B.coordinates.symm.injOn.comp hgi hgmap)
      (fun z hz => B.source_subset (hsource z hz))
  · exact fun z hz => B.chart.map_target (B.source_subset (hsource z hz))
  · intro z hz
    rw [Function.comp_apply, hchart z hz]
    exact hsource z hz
  · intro x hx
    have hg0 : g (x, 0) = q x := Prod.ext rfl (by simpa [g] using (hfirst x hx).1.symm)
    change B.chart.symm (B.coordinates.symm (g (x, 0))) = p x
    rw [hg0]
    exact (congrArg B.chart.symm (B.coordinates.left_inv (hpc hx))).trans
      (B.chart.left_inv (hps hx))
  · intro z hz
    have h := B.first_surface (B.coordinates.symm (g z)) (hsource z hz)
    rw [B.coordinates.right_inv (hgmap hz)] at h
    change F z ∈ S ↔ _ at h
    simpa only [g, mul_eq_zero, hδ.ne', false_or, true_implies,
      (hfirst z.1 hz.1).2, and_true] using h
  · intro z hz
    have h := B.second_surface (B.coordinates.symm (g z)) (hsource z hz)
    rw [B.coordinates.right_inv (hgmap hz)] at h
    have h0 := B.second_surface (B.chart (p z.1)) (hpc hz.1)
    rw [B.chart.left_inv (hps hz.1)] at h0
    exact h.trans h0.symm

end PoincareConjecture.M76
