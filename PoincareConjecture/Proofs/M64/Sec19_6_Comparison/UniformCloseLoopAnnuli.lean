import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.CanonicalAnnulusConstructor
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.CloseLoopInterpolator
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.SampledInterpolatorVertical












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture




theorem m64_uniform_close_loop_canonical_annuli
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
    {a b : ℝ} (F : RicciFlow 3 M (Icc a b)) (t : ℝ)
    (hcompact : IsCompact (univ : Set M))
    {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]
    (Gamma : Z → C1FreeLoopSpace (M := M)) (hGamma : Continuous Gamma)
    {mu : ℝ} (hmu : 0 < mu) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ z w : Z,
      (∀ x : ℝ, (F.metric t).edist (periodicFreeLoop (Gamma z) x)
        (periodicFreeLoop (Gamma w) x) < ENNReal.ofReal epsilon) →
      ∀ circumference : ℝ, ∀ P : M62.CircleProductData F circumference,
        circumference ≤ curvePeriod →
        ∃ A : M64Annulus (P.flow.metric t)
          (m63CanonicalRamp P (periodicFreeLoop (Gamma z)))
          (m63CanonicalRamp P (periodicFreeLoop (Gamma w))), A.area < mu := by
  let g := F.metric t
  obtain ⟨r, hr, H, hH, hgeom, _hdiag, _hunique⟩ :=
    M63.exists_smooth_minimizing_interpolator g hcompact
  obtain ⟨S, _hS, hspeed⟩ := m64_compact_family_speed_bound g Gamma hGamma
  obtain ⟨B, hB, hbound⟩ :=
    m64_interpolator_endpoint_bound_on_short_tube g hcompact hr H hH S
  let C := (B + 1) * volume.real m64AnnulusDomain
  have hC : 0 ≤ C := mul_nonneg (by linarith) ENNReal.toReal_nonneg
  have hdenom : 0 < C + 1 := by linarith
  let epsilon := min (r / 2) (mu / (C + 1))
  have hepsilon : 0 < epsilon := lt_min (half_pos hr) (div_pos hmu hdenom)
  have hepsr : epsilon ≤ r / 2 := min_le_left _ _
  have hstrict : (B + 1) * epsilon * volume.real m64AnnulusDomain < mu := by
    calc
      _ = C * epsilon := by dsimp only [C]; ring
      _ < (C + 1) * epsilon := by nlinarith
      _ ≤ mu := by
        have h := (le_div_iff₀ hdenom).mp (min_le_right (r / 2) (mu / (C + 1)))
        nlinarith only [h]
  refine ⟨epsilon, hepsilon, ?_⟩
  intro z w hshort circumference P hcirc
  have hshortHalf (x : ℝ) : g.edist (periodicFreeLoop (Gamma z) x)
      (periodicFreeLoop (Gamma w) x) < ENNReal.ofReal (r / 2) :=
    (hshort x).trans_le (ENNReal.ofReal_le_ofReal hepsr)
  have hshortR (x : ℝ) : g.edist (periodicFreeLoop (Gamma z) x)
      (periodicFreeLoop (Gamma w) x) < ENNReal.ofReal r :=
    (hshortHalf x).trans ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))
  let f : LoopPlane → M := fun p =>
    H (p 1, periodicFreeLoop (Gamma z) (p 0), periodicFreeLoop (Gamma w) (p 0))
  have hHat : ∀ p ∈ m64AnnulusDomain,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 H
        (p 1, periodicFreeLoop (Gamma z) (p 0), periodicFreeLoop (Gamma w) (p 0)) := by
    intro p hp
    have htime : p 1 ∈ Ioo (-1 : ℝ) 2 := by
      constructor <;> linarith [hp.2.2.1, hp.2.2.2]
    have hmem : (p 1, periodicFreeLoop (Gamma z) (p 0), periodicFreeLoop (Gamma w) (p 0)) ∈
        Ioo (-1 : ℝ) 2 ×ˢ {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r} :=
      ⟨htime, hshortR (p 0)⟩
    exact (hH.contMDiffAt ((isOpen_Ioo.prod (m64_isOpen_short_pair_tube g r)).mem_nhds
      hmem)).of_le (m := 1) (by norm_num)
  have hf : ∀ p ∈ m64AnnulusDomain, ContMDiffAt (𝓡 2) (𝓡 3) 1 f p :=
    fun p hp => m64_pair_interpolator_contMDiffAt (Gamma z) (Gamma w) (hHat p hp)
  have hcolumns : ∀ p ∈ m64AnnulusDomain,
      g.tangentNorm (f p)
          (mfderiv (𝓡 2) (𝓡 3) f p (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ≤ B ∧
      g.tangentNorm (f p)
          (mfderiv (𝓡 2) (𝓡 3) f p (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ≤ epsilon := by
    intro p hp
    apply m64_pair_interpolator_column_bounds g (Gamma z) (Gamma w) hHat
      ?_ (hspeed z) (hspeed w) ?_ hshort hp
    · intro q hq v hv v' hv'
      exact hbound (q 1) ⟨hq.2.2.1, hq.2.2.2⟩ _ _ (hshortHalf (q 0)).le v hv v' hv'
    · intro x s hs
      exact (hgeom _ _ (hshortR x)).2.2.2.1 s
        ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s) := by
    intro x s
    change H (s, periodicFreeLoop (Gamma z) (x + curvePeriod),
      periodicFreeLoop (Gamma w) (x + curvePeriod)) = _
    have hz : periodicFreeLoop (Gamma z) (x + curvePeriod) = periodicFreeLoop (Gamma z) x :=
      Proofs.M58.periodic_periodicFreeLoop (Gamma z) x
    have hw : periodicFreeLoop (Gamma w) (x + curvePeriod) = periodicFreeLoop (Gamma w) x :=
      Proofs.M58.periodic_periodicFreeLoop (Gamma w) x
    rw [hz, hw]
    rfl
  have hlower (x : ℝ) : f (annulusPoint x 0) = periodicFreeLoop (Gamma z) x :=
    (hgeom _ _ (hshortR x)).1
  have hupper (x : ℝ) : f (annulusPoint x 1) = periodicFreeLoop (Gamma w) x :=
    (hgeom _ _ (hshortR x)).2.1
  obtain ⟨A, _, hA⟩ := m64_canonical_annulus_of_columns P t f hf hperiodic
    hlower hupper hB hepsilon.le (fun p hp => (hcolumns p hp).1)
      (fun p hp => (hcolumns p hp).2) hcirc hstrict
  exact ⟨A, hA⟩

end PoincareConjecture
