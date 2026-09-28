import PoincareConjecture.Proofs.M47.LimitCanonicalComponentCurvature
import PoincareConjecture.Proofs.M47.LimitCanonicalAlternative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open M04

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {V : GeneralizedBlowupSequence.{u}}
  (G : GeneralizedBlowupConvergence V (blowupBackwardInterval ⊤))

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold




theorem limitCanonical_component_eventually_sectional_fields
    (P : M47Predecessors.{u}) (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (V.flow i) (F i))
    {kappa C : ℝ} (hkappa : 0 < kappa)
    (hnc : BlowupLimitNoncollapsed G.limit kappa) :
    letI : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
    let K : AncientKappaSolution 3 G.limit.sliceCarrier.carrier :=
      (limitAncientIdentification P.m04 G.limit kappa hkappa hnc).certificate.solution
    ∀ _N : M27CanonicalComponent K 0 C,
      ∃ a : ℝ, 0 < a ∧
        (∀ x : G.limit.sliceCarrier.carrier, ∀ u v : TangentSpace (𝓡 3) x,
          LeviCivitaData.IsOrthonormalPair (G.limit.flow.metric 0) x u v →
            a < (G.limit.flow.connection 0).sectionalCurvature x u v) ∧
        ∀ᶠ k in atTop,
          let f := limitCanonicalPhysicalTerminalChart G F R k
          let g := M13.scaleSmoothMetric
            ((F (G.subsequence k)).metric
              ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
            (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
          let D := M13.scaleLeviCivitaData
            ((F (G.subsequence k)).connection
              ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
            (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
          G.exhaustion.space k = univ ∧
            f.target = connectedComponent (f G.limit.base) ∧
            0 < scalarCurvatureSupOn g D f.target ∧
            ∀ y ∈ f.target, ∀ u v : TangentSpace (𝓡 3) y,
              LeviCivitaData.IsOrthonormalPair g y u v →
                0 < D.sectionalCurvature y u v ∧
                  C⁻¹ * scalarCurvatureSupOn g D f.target < D.sectionalCurvature y u v := by
  let : ConnectedSpace G.limit.sliceCarrier.carrier := G.limit.connectedSpace
  dsimp only
  intro N
  let : CompactSpace G.limit.carrier.carrier := isCompact_univ_iff.mp N.compact
  let R0 := scalarCurvatureSup (G.limit.flow.metric 0) (G.limit.flow.connection 0)
  have hR0 : 0 < R0 := N.scalar_sup_pos
  have hC : 0 < C := N.constant_pos
  obtain ⟨B, hB, hsectional⟩ := N.uniform_sectional_lower
  obtain ⟨a, ha, haB⟩ := exists_between (mul_lt_mul_of_pos_right hB hR0)
  have ha0 : 0 < a := (mul_pos (inv_pos.mpr hC) hR0).trans ha
  let eta := (C * a - R0) / 2
  have hgap : R0 < C * a := by
    have h := mul_lt_mul_of_pos_left ha hC
    simpa only [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] using h
  have heta : 0 < eta := by dsimp only [eta]; linarith
  have hmargin : C⁻¹ * (R0 + eta) < a := by
    calc
      _ < C⁻¹ * (C * a) := mul_lt_mul_of_pos_left (by dsimp only [eta]; linarith)
        (inv_pos.mpr hC)
      _ = a := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
  have hsec (x : G.limit.sliceCarrier.carrier) (u v : TangentSpace (𝓡 3) x)
      (huv : LeviCivitaData.IsOrthonormalPair (G.limit.flow.metric 0) x u v) :
      a < (G.limit.flow.connection 0).sectionalCurvature x u v :=
    haB.trans_le (hsectional x u v huv.1 huv.2.1 huv.2.2)
  have hbounded : BddAbove (range (G.limit.flow.connection 0).scalarCurvature) :=
    (isCompact_range
      (M34.contMDiff_scalarCurvature (G.limit.flow.connection 0)).continuous).bddAbove
  have hscalar (x : G.limit.sliceCarrier.carrier) :
      (G.limit.flow.connection 0).scalarCurvature x ≤ R0 :=
    le_csSup hbounded (mem_range_self x)
  refine ⟨a, ha0, hsec, ?_⟩
  filter_upwards [limitCanonical_component_eventually_physical_curvature
    G P F R N.compact a hsec heta] with k hk
  let f := limitCanonicalPhysicalTerminalChart G F R k
  let g : RiemannianMetric 3
      ((F (G.subsequence k)).slice
        ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k))).carrier :=
    M13.scaleSmoothMetric ((F (G.subsequence k)).metric
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
      (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
  let D : LeviCivitaData g := M13.scaleLeviCivitaData
    ((F (G.subsequence k)).connection
      ((V.base (G.subsequence k)).1 + 0 / V.scale (G.subsequence k)))
    (V.scale (G.subsequence k)) (V.base_scalar_pos (G.subsequence k))
  have hsource : f.source = univ :=
    (limitCanonicalPhysicalChart_source _ _ _ _ _ _).trans hk.1
  have hupper (y : f.target) : D.scalarCurvature y.val ≤ R0 + eta := by
    have herror := (hk.2.2 (f.toPartialEquiv.symm y.val)).2.2
    change |D.scalarCurvature (f.toPartialEquiv (f.toPartialEquiv.symm y.val)) -
      (G.limit.flow.connection 0).scalarCurvature (f.toPartialEquiv.symm y.val)| < eta at herror
    rw [f.toPartialEquiv.right_inv y.property] at herror
    have h := (abs_lt.mp herror).2
    exact (by linarith [hscalar (f.toPartialEquiv.symm y.val)] :
      D.scalarCurvature y.val < R0 + eta).le
  have hnewbounded : BddAbove (range (fun y : f.target => D.scalarCurvature y.val)) :=
    ⟨R0 + eta, by rintro z ⟨y, rfl⟩; exact hupper y⟩
  let y0 : f.target := ⟨f G.limit.base, f.map_source (hsource ▸ mem_univ _)⟩
  have hsup : scalarCurvatureSupOn g D f.target ≤ R0 + eta :=
    csSup_le ⟨D.scalarCurvature y0.val, mem_range_self y0⟩
      (by rintro z ⟨y, rfl⟩; exact hupper y)
  have hpos : 0 < scalarCurvatureSupOn g D f.target := by
    have hlow : 6 * a ≤ D.scalarCurvature y0.val := (hk.2.2 G.limit.base).2.1
    exact (mul_pos (by norm_num : (0 : ℝ) < 6) ha0).trans_le
      (hlow.trans (le_csSup hnewbounded (mem_range_self y0)))
  refine ⟨hk.1, hk.2.1, hpos, ?_⟩
  intro y hy u v huv
  change g.inner y u u = 1 ∧ g.inner y v v = 1 ∧ g.inner y u v = 0 at huv
  have hall := (hk.2.2 (f.toPartialEquiv.symm y)).1
  change ∀ u v : TangentSpace (𝓡 3) (f.toPartialEquiv (f.toPartialEquiv.symm y)),
    a * metricGram g (f.toPartialEquiv (f.toPartialEquiv.symm y)) u v ≤
      D.curvatureTensor (f.toPartialEquiv (f.toPartialEquiv.symm y)) u v u v at hall
  rw [f.toPartialEquiv.right_inv hy] at hall
  have hplane : a ≤ D.sectionalCurvature y u v := by
    simpa only [LeviCivitaData.sectionalCurvature, metricGram, huv.1, huv.2.1,
      huv.2.2, one_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one, div_one]
      using hall u v
  exact ⟨ha0.trans_le hplane,
    ((mul_le_mul_of_nonneg_left hsup (inv_pos.mpr hC).le).trans_lt hmargin).trans_le hplane⟩

end PoincareConjecture.M47
