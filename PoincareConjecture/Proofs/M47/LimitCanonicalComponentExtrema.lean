import PoincareConjecture.Proofs.M47.LimitCanonicalComponentScalarRadius

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

theorem limitCanonical_real_extrema_of_uniform_error
    {X : Type v} [Nonempty X] (f g : X → ℝ)
    (hupper : BddAbove (range f)) (hlower : BddBelow (range f))
    {eta : ℝ} (herror : ∀ x, |g x - f x| ≤ eta) :
    BddAbove (range g) ∧ BddBelow (range g) ∧
      |sSup (range g) - sSup (range f)| ≤ eta ∧
      |sInf (range g) - sInf (range f)| ≤ eta := by
  obtain ⟨U, hU⟩ := hupper
  obtain ⟨L, hL⟩ := hlower
  have hfup : BddAbove (range f) := ⟨U, hU⟩
  have hflo : BddBelow (range f) := ⟨L, hL⟩
  have hgup : BddAbove (range g) := by
    refine ⟨U + eta, ?_⟩
    rintro z ⟨x, rfl⟩
    linarith [(abs_le.mp (herror x)).2, hU (mem_range_self x)]
  have hglo : BddBelow (range g) := by
    refine ⟨L - eta, ?_⟩
    rintro z ⟨x, rfl⟩
    linarith [(abs_le.mp (herror x)).1, hL (mem_range_self x)]
  have hsu : sSup (range g) ≤ sSup (range f) + eta := by
    apply csSup_le (range_nonempty g)
    rintro z ⟨x, rfl⟩
    linarith [(abs_le.mp (herror x)).2, le_csSup hfup (mem_range_self x)]
  have hsu' : sSup (range f) ≤ sSup (range g) + eta := by
    apply csSup_le (range_nonempty f)
    rintro z ⟨x, rfl⟩
    linarith [(abs_le.mp (herror x)).1, le_csSup hgup (mem_range_self x)]
  have hin : sInf (range f) - eta ≤ sInf (range g) := by
    apply le_csInf (range_nonempty g)
    rintro z ⟨x, rfl⟩
    linarith [(abs_le.mp (herror x)).1, csInf_le hflo (mem_range_self x)]
  have hin' : sInf (range g) - eta ≤ sInf (range f) := by
    apply le_csInf (range_nonempty f)
    rintro z ⟨x, rfl⟩
    linarith [(abs_le.mp (herror x)).2, csInf_le hglo (mem_range_self x)]
  exact ⟨hgup, hglo, abs_le.mpr ⟨by linarith, by linarith⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩⟩

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

theorem limitCanonical_component_eventually_radius_extrema
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    (hcompact : IsCompact (univ : Set G.limit.sliceCarrier.carrier))
    {a : ℝ} (ha : 0 < a) (hsec : ∀ x : G.limit.sliceCarrier.carrier,
      ∀ u v : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair (G.limit.flow.metric 0) x u v →
          a < (G.limit.flow.connection 0).sectionalCurvature x u v)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ k in atTop,
      let f := limitCanonicalPhysicalTerminalChart G F R k
      let D := M13.scaleLeviCivitaData
        ((F (G.subsequence k)).connection
          ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
        (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
      let old := range (fun x : G.limit.sliceCarrier.carrier =>
        (G.limit.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ))
      let new := range (fun y : f.target => D.scalarCurvature y.val ^ (-1 / 2 : ℝ))
      G.exhaustion.space k = univ ∧
        f.target = connectedComponent (f G.limit.base) ∧
        BddAbove new ∧ BddBelow new ∧
        |sSup new - sSup old| ≤ eta ∧ |sInf new - sInf old| ≤ eta := by
  let : CompactSpace G.limit.carrier.carrier := isCompact_univ_iff.mp hcompact
  let : CompactSpace G.limit.sliceCarrier.carrier := isCompact_univ_iff.mp hcompact
  let : Nonempty G.limit.sliceCarrier.carrier := ⟨G.limit.base⟩
  let r0 := fun x : G.limit.sliceCarrier.carrier =>
    (G.limit.flow.connection 0).scalarCurvature x ^ (-1 / 2 : ℝ)
  have hpos (x : G.limit.carrier.carrier) :
      0 < (G.limit.flow.connection 0).scalarCurvature x :=
    (mul_pos (by norm_num : (0 : ℝ) < 6) ha).trans
      (six_mul_lt_scalar_of_sectional_lower (G.limit.flow.connection 0) x a (hsec x))
  have hcontinuous : Continuous r0 :=
    (M34.contMDiff_scalarCurvature (G.limit.flow.connection 0)).continuous.rpow_const
      (fun x => Or.inl (hpos x).ne')
  have hbounded : BddAbove (range r0) ∧ BddBelow (range r0) :=
    ⟨(isCompact_range hcontinuous).bddAbove, (isCompact_range hcontinuous).bddBelow⟩
  have hconv := limitCanonical_component_scalar_radius_convergence G P F R hcompact ha hsec
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv eta heta,
    limitCanonical_eventually_physical_component_image G F R hcompact] with k hk hfull
  let f := limitCanonicalPhysicalTerminalChart G F R k
  let D := M13.scaleLeviCivitaData
    ((F (G.subsequence k)).connection
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
    (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
  let r := fun x : G.limit.sliceCarrier.carrier => D.scalarCurvature (f x) ^ (-1 / 2 : ℝ)
  have herror (x : G.limit.sliceCarrier.carrier) : |r x - r0 x| ≤ eta := by
    have he : |r0 x - r x| < eta := by
      simpa only [Real.dist_eq] using hk x (mem_univ x)
    rw [abs_sub_comm] at he
    exact he.le
  have hext := limitCanonical_real_extrema_of_uniform_error r0 r
    hbounded.1 hbounded.2 herror
  have hsource : f.source = univ :=
    (limitCanonicalPhysicalChart_source _ _ _ _ _ _).trans hfull.1
  have hrange : range r = range (fun y : f.target => D.scalarCurvature y.val ^ (-1 / 2 : ℝ)) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨f x, f.map_source (hsource ▸ mem_univ x)⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨f.toPartialEquiv.symm y.val, ?_⟩
      exact congrArg (fun z => D.scalarCurvature z ^ (-1 / 2 : ℝ))
        (f.toPartialEquiv.right_inv y.property)
  rw [hrange] at hext
  exact ⟨hfull.1, hfull.2 0
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
    (limitCanonical_terminal_clock_mem G k), hext⟩

end PoincareConjecture.M47
