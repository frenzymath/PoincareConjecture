import PoincareConjecture.Proofs.M09.CompactDerivativeExtension
import PoincareConjecture.Proofs.M09.VariationFieldSmooth









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T a b : ℝ} {p : BackwardTimePath F T a b}

local notation "Q" => EuclideanSpace ℝ (Fin n)

theorem variation_baseSquareCurve_eq (V : LVariation F T a b p)
    (s : ℝ) (hs : s ∈ sqrtParameterInterval a b) :
    V.baseSquareCurve s = p.curve (s ^ 2) :=
  (V.square_agrees s hs 0 ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩).trans
    (V.at_zero (s ^ 2))

set_option backward.isDefEq.respectTransparency false in
theorem squareVariationField_eq_variationField (V : LVariation F T a b p)
    (s : ℝ) (hs : s ∈ sqrtParameterInterval a b) :
    (squareVariationField V s : Q) = variationField V (s ^ 2) := by
  have heq : V.squareFamily s =ᶠ[𝓝 (0 : ℝ)] V.family (s ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds
      (show (0 : ℝ) ∈ Set.Ioo (-V.radius) V.radius from
        ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩)] with u hu
    exact V.square_agrees s hs u hu
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
  have hv := congrArg (fun L : ℝ →L[ℝ] Q ↦ L 1) hd
  have hcast (x y : M) (h : x = y) (v : TangentSpace (𝓡 n) x) :
      (h ▸ v : TangentSpace (𝓡 n) y) = (show TangentSpace (𝓡 n) y from v) := by
    cases h
    rfl
  unfold variationField
  rw [hcast]
  exact hv

theorem exists_sqrtRegularField_of_variation_extension (τmax : ℝ) (hτmax : 0 < τmax)
    (hmax : b < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (R : SqrtRegularPath p) (V : LVariation F T a b p)
    (E : ParametricAlongCurveExtensionOn (sqrtParameterInterval a b)
      V.baseSquareCurve (squareVariationField V)) :
    ∃ D : SqrtRegularField R (variationField V),
      ∀ s ∈ sqrtParameterInterval a b,
        (D.firstDerivative s : Q) = pullbackCovariantDerivative F (fun r ↦ T - r ^ 2)
          V.baseSquareCurve (squareVariationField V) (sqrtParameterInterval a b) E s := by
  let K := sqrtParameterInterval a b
  have hbase (s : ℝ) (hs : s ∈ K) : R.curve s = V.baseSquareCurve s :=
    (R.agrees s hs).trans (variation_baseSquareCurve_eq V s hs).symm
  let Y : ∀ s, TangentSpace (𝓡 n) (R.curve s) := fun s ↦ E.extension s (R.curve s)
  let E' : ParametricAlongCurveExtensionOn K R.curve Y := {
    extension := E.extension
    domain := E.domain
    open_domain := E.open_domain
    graph_mem := by
      intro s hs
      rw [hbase s hs]
      exact E.graph_mem s hs
    smooth := E.smooth
    agrees := fun _ _ ↦ rfl
  }
  have hKd : UniqueDiffOn ℝ K := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
  have htime : K ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) := by
    intro s hs
    exact ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le
      ((Real.sqrt_nonneg a).trans hs.1),
      hs.2.trans_lt (Real.sqrt_lt_sqrt (p.nonnegative.trans p.ordered.le) hmax)⟩
  obtain ⟨E2⟩ := nonempty_pullbackDerivativeExtensionOn_compact F T τmax hτmax hwindow
    R.curve Y R.domain K R.open_domain R.interval_subset isCompact_Icc hKd htime R.smooth E'
  let D : SqrtRegularField R (variationField V) := {
    field := Y
    agrees := by
      intro s hs
      have hcast (x y : M) (h : x = y) (v : TangentSpace (𝓡 n) x) :
          (h ▸ v : TangentSpace (𝓡 n) y) = (show TangentSpace (𝓡 n) y from v) := by
        cases h
        rfl
      rw [hcast]
      change (E.extension s (R.curve s) : Q) = variationField V (s ^ 2)
      rw [hbase s hs]
      exact (E.agrees s hs).trans (squareVariationField_eq_variationField V s hs)
    extension := E'
    derivative_extension := E2
  }
  refine ⟨D, ?_⟩
  intro s hs
  have hd := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
    (fun r hr ↦ hbase r hr) hs
  have hvel : (curveVelocityWithin (n := n) R.curve K s : Q) =
      curveVelocityWithin (n := n) V.baseSquareCurve K s :=
    congrArg (fun L : ℝ →L[ℝ] Q ↦ L 1) hd
  change (deriv (fun r ↦ E.extension r (R.curve s)) s +
      (F.connection (T - s ^ 2)).connection (E.extension s) (R.curve s)
        (curveVelocityWithin (n := n) R.curve K s) : Q) =
    deriv (fun r ↦ E.extension r (V.baseSquareCurve s)) s +
      (F.connection (T - s ^ 2)).connection (E.extension s) (V.baseSquareCurve s)
        (curveVelocityWithin (n := n) V.baseSquareCurve K s)
  rw [hvel, hbase s hs]

theorem nonempty_variationFieldExtension (V : LVariation F T a b p) :
    Nonempty (ParametricAlongCurveExtensionOn (sqrtParameterInterval a b)
      V.baseSquareCurve (squareVariationField V)) := by
  let U := (fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' V.squareDomain
  obtain ⟨hU, hKU, hY⟩ := squareVariationField_smooth V
  have hf : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞
      (fun z ↦ V.squareFamily z.1 z.2) V.squareDomain := by
    convert! V.square_smooth using 1 <;>
      simp only [modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hi : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ × ℝ)) ∞ (fun s : ℝ ↦ (s, (0 : ℝ))) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  have hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ V.baseSquareCurve U :=
    hf.comp hi.contMDiffOn (fun s hs ↦ hs)
  exact nonempty_parametricFieldExtensionOn_compact V.baseSquareCurve (squareVariationField V)
    U (sqrtParameterInterval a b) hU hKU isCompact_Icc hγ hY

theorem nonempty_sqrtRegularField_variation (τmax : ℝ) (hτmax : 0 < τmax)
    (hmax : b < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (R : SqrtRegularPath p) (V : LVariation F T a b p) :
    Nonempty (SqrtRegularField R (variationField V)) := by
  obtain ⟨E⟩ := nonempty_variationFieldExtension V
  obtain ⟨D, _⟩ := exists_sqrtRegularField_of_variation_extension τmax hτmax hmax hwindow R V E
  exact ⟨D⟩

end PoincareConjecture.Proofs.M09
