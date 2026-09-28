import PoincareConjecture.Proofs.M47.PositiveGradientTerminal
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Restriction
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveLocalIsometry

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47Positive

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {J : Set ℝ}

def zeroBasedHalfOpenRestriction (F : RicciFlow 3 M J)
    {a b : ℝ} (hab : a < b) (hI : Ico a b ⊆ J) : RicciFlow 3 M (Ico 0 (b - a)) where
  metric s := F.metric (a + s)
  connection s := F.connection (a + s)
  interval := ordConnected_Ico
  nontrivial := ⟨0, ⟨le_rfl, sub_pos.mpr hab⟩,
    (b - a) / 2, ⟨by linarith, by linarith⟩, by linarith⟩
  smooth := by
    have hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞
        (fun p : ℝ × M => (a + p.1, p.2)) :=
      (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
    exact F.smooth.comp hs.contMDiffOn (fun p hp =>
      ⟨hI ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, mem_univ _⟩)
  equation s hs x v w := by
    have htime : a + s ∈ J := hI ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hshift : HasDerivWithinAt (fun t : ℝ => a + t) 1 (Ico 0 (b - a)) s := by
      simpa only [id_eq] using ((hasDerivAt_id s).const_add a).hasDerivWithinAt
    have h := (F.equation (a + s) htime x v w).comp s hshift
      (fun t ht => hI ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    convert! h using 1
    simp only [mul_one]

theorem positive_blowup_on_interval
    [CompactSpace M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M J)
    {a b : ℝ} (hab : a < b) (hI : Ico a b ⊆ J)
    (hpos : ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric a) x v w →
        0 < (F.connection a).sectionalCurvature x v w)
    (hblow : ∀ L s : ℝ, s < b → ∃ t ∈ Ioo (max a s) b, ∃ x : M,
      L < (F.connection t).curvatureTensorNorm x) :
    ∀ L : ℝ, ∃ s ∈ Ico a b, ∀ t ∈ Ioo s b, ∀ x : M,
      L ≤ (F.connection t).scalarCurvature x := by
  let G := zeroBasedHalfOpenRestriction F hab hI
  have hposG : ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (G.metric 0) x v w →
        0 < (G.connection 0).sectionalCurvature x v w := by
    change ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric (a + 0)) x v w →
        0 < (F.connection (a + 0)).sectionalCurvature x v w
    exact (congrArg (fun t => ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric t) x v w →
        0 < (F.connection t).sectionalCurvature x v w) (add_zero a)).mpr hpos
  have hblowG : ∀ L s : ℝ, s < b - a → ∃ t ∈ Ioo (max 0 s) (b - a), ∃ x : M,
      L < (G.connection t).curvatureTensorNorm x := by
    intro L s hs
    obtain ⟨t, ht, x, hx⟩ := hblow L (a + s) (by linarith)
    have hta := (le_max_left a (a + s)).trans_lt ht.1
    have hts := (le_max_right a (a + s)).trans_lt ht.1
    refine ⟨t - a, ⟨max_lt (by linarith) (by linarith), by linarith [ht.2]⟩, x, ?_⟩
    change L < (F.connection (a + (t - a))).curvatureTensorNorm x
    exact (congrArg (fun z => L < (F.connection z).curvatureTensorNorm x)
      (show a + (t - a) = t by ring)).mpr hx
  intro L
  obtain ⟨s, hs0, hsb, hfloor⟩ :=
    positive_component_blowup hC M (b - a) (sub_pos.mpr hab) G hposG hblowG L
  refine ⟨a + s, ⟨by linarith, by linarith⟩, ?_⟩
  intro t ht x
  have h := hfloor (t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x
  change L ≤ (F.connection (a + (t - a))).scalarCurvature x at h
  exact (congrArg (fun z => L ≤ (F.connection z).scalarCurvature x)
    (show a + (t - a) = t by ring)).mp h

theorem positive_blowup_on_component
    [CompactSpace M] [T3Space M] [SecondCountableTopology M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M J) (p : M)
    {a b : ℝ} (hab : a < b) (hI : Ico a b ⊆ J)
    (hpos : ∀ x ∈ connectedComponent p, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric a) x v w →
        0 < (F.connection a).sectionalCurvature x v w)
    (hblow : ∀ L s : ℝ, s < b → ∃ t ∈ Ioo (max a s) b,
      ∃ x ∈ connectedComponent p, L < (F.connection t).curvatureTensorNorm x) :
    ∀ L : ℝ, ∃ s ∈ Ico a b, ∀ t ∈ Ioo s b, ∀ x ∈ connectedComponent p,
      L ≤ (F.connection t).scalarCurvature x := by
  let U := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
  let : CompactSpace U := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  let G := F.restrictComponent p
  have hposG : ∀ x : U, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (G.metric a) x v w →
        0 < (G.connection a).sectionalCurvature x v w := by
    intro x
    exact (Proofs.M46.sectional_positive_iff_of_local_isometry (G.connection a) (F.connection a)
      (f := (Subtype.val : U → M)) isOpen_univ contMDiff_subtype_val.contMDiffOn
      (fun y _ v w => F.restrictComponent_inner p a y v w) (mem_univ x)).mpr (hpos x x.2)
  have hblowG : ∀ L s : ℝ, s < b → ∃ t ∈ Ioo (max a s) b, ∃ x : U,
      L < (G.connection t).curvatureTensorNorm x := by
    intro L s hs
    obtain ⟨t, ht, x, hx, hcurv⟩ := hblow L s hs
    refine ⟨t, ht, ⟨x, hx⟩, ?_⟩
    simpa only [G, F.restrictComponent_curvatureTensorNorm] using hcurv
  intro L
  obtain ⟨s, hs, hfloor⟩ := positive_blowup_on_interval hC G hab hI hposG hblowG L
  refine ⟨s, hs, ?_⟩
  intro t ht x hx
  simpa only [G, F.restrictComponent_scalarCurvature] using hfloor t ht ⟨x, hx⟩

end PoincareConjecture.M47Positive
