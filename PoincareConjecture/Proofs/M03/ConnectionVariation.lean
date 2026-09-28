import PoincareConjecture.Proofs.M03.ConnectionPairingEvolution
import PoincareConjecture.Proofs.M03.CurvatureVectorTime









set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem ricciFlow_connection_variation_pairing
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {U : Set M} (hU : IsOpen U)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric 0).toRiemannianMetric⟩
    let c := extChartAt (𝓡 n) x
    let r := fun y (a b : TangentSpace (𝓡 n) y) =>
      (F.connection t).ricci y a b
    let cr := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) =>
      fderiv ℝ (fun z => r (c.symm z) (B (c.symm z)) (C (c.symm z)))
          (c x) (A x) -
        r x ((F.connection t).connection B x (A x)) (C x) -
        r x (B x) ((F.connection t).connection C x (A x))
    let V := fun s => (F.connection s).connection Y x (X x)
    HasDerivAt V (deriv V t) t ∧
      (F.metric t).inner x (deriv V t) (Z x) =
        -cr X Y Z - cr Y Z X + cr Z X Y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric 0).toRiemannianMetric⟩
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x →L[ℝ] ℝ) := inferInstance
  let c := extChartAt (𝓡 n) x
  let r := fun y (a b : TangentSpace (𝓡 n) y) =>
    (F.connection t).ricci y a b
  let cr := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) =>
    fderiv ℝ (fun z => r (c.symm z) (B (c.symm z)) (C (c.symm z)))
        (c x) (A x) -
      r x ((F.connection t).connection B x (A x)) (C x) -
      r x (B x) ((F.connection t).connection C x (A x))
  let V := fun s => (F.connection s).connection Y x (X x)
  change HasDerivAt V (deriv V t) t ∧
    (F.metric t).inner x (deriv V t) (Z x) =
      -cr X Y Z - cr Y Z X + cr Z X Y
  have htJ : J ∈ 𝓝 t := mem_interior_iff_mem_nhds.mp ht
  have hV : HasDerivAt V (deriv V t) t := by
    have hs := contMDiffOn_connection_family_apply F.smooth F.connection hU Y X hY hX
    have hi : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun s : ℝ => (s, x)) t := contMDiffAt_id.prodMk contMDiffAt_const
    have hsAt := (hs.contMDiffAt (prod_mem_nhds htJ (hU.mem_nhds hx))).comp t hi
    let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
    have he : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    let L := e.continuousLinearEquivAt ℝ x he
    have hc : ContDiffAt ℝ ∞ (fun s => L (V s)) t :=
      (Bundle.contMDiffAt_totalSpace.mp hsAt).2.contDiffAt
    have hv := L.symm.contDiff.contDiffAt.comp t hc
    have hv' : ContDiffAt ℝ ∞ V t := by
      simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hv
    exact (hv'.differentiableAt (by simp)).hasDerivAt
  refine ⟨hV, ?_⟩
  let G (s : ℝ) : TangentSpace (𝓡 n) x →L[ℝ]
      TangentSpace (𝓡 n) x →L[ℝ] ℝ := (F.metric s).inner x
  have hG : HasDerivAt G (deriv G t) t :=
    (((contDiffOn_family_metric_inner_time F.smooth x).contDiffAt htJ).differentiableAt
      (by simp)).hasDerivAt
  have he (a b : TangentSpace (𝓡 n) x) :
      HasDerivAt (fun s => (F.metric s).inner x a b) (-2 * r x a b) t :=
    (F.equation t (interior_subset ht) x a b).hasDerivAt htJ
  have hq (a b : TangentSpace (𝓡 n) x) : (deriv G t) a b = -2 * r x a b := by
    have hd := (hG.clm_apply (hasDerivAt_const t a)).clm_apply (hasDerivAt_const t b)
    have hd' : HasDerivAt (fun s => (F.metric s).inner x a b) ((deriv G t) a b) t := by
      simpa only [map_zero, add_zero] using hd
    exact hd'.unique (he a b)
  have hprod : HasDerivAt
      (fun s => 2 * (F.metric s).inner x (V s) (Z x))
      (2 * (-2 * r x (V t) (Z x) + (F.metric t).inner x (deriv V t) (Z x))) t := by
    have hd := ((hG.clm_apply hV).clm_apply (hasDerivAt_const t (Z x))).const_mul 2
    simpa only [map_zero, add_zero, add_apply, hq] using hd
  have hscale (B C : (y : M) → TangentSpace (𝓡 n) y)
      (a : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun z => -2 * r (c.symm z) (B (c.symm z)) (C (c.symm z)))
          (c x) a =
        -2 * fderiv ℝ (fun z => r (c.symm z) (B (c.symm z)) (C (c.symm z)))
          (c x) a := by
    change fderiv ℝ ((-2 : ℝ) •
      (fun z => r (c.symm z) (B (c.symm z)) (C (c.symm z)))) (c x) a = _
    rw [fderiv_const_smul_field]
    rfl
  have hk := (hasDerivAt_ricciFlow_koszul_pairing F ht hU X Y Z hX hY hZ hx).unique hprod
  change
    fderiv ℝ (fun z => -2 * r (c.symm z) (Y (c.symm z)) (Z (c.symm z))) (c x) (X x) +
    fderiv ℝ (fun z => -2 * r (c.symm z) (Z (c.symm z)) (X (c.symm z))) (c x) (Y x) -
    fderiv ℝ (fun z => -2 * r (c.symm z) (X (c.symm z)) (Y (c.symm z))) (c x) (Z x) +
    -2 * r x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) -
    -2 * r x (Y x) (VectorField.mlieBracket (𝓡 n) X Z x) -
    -2 * r x (X x) (VectorField.mlieBracket (𝓡 n) Y Z x) =
      2 * (-2 * r x (V t) (Z x) + (F.metric t).inner x (deriv V t) (Z x)) at hk
  rw [hscale Y Z (X x), hscale Z X (Y x), hscale X Y (Z x)] at hk
  have hsub₁ (a b z : TangentSpace (𝓡 n) x) :
      r x (a - b) z = r x a z - r x b z := by
    have hh : (deriv G t) (a - b) z = (deriv G t) a z - (deriv G t) b z := by
      rw [map_sub, sub_apply]
    rw [hq, hq, hq] at hh
    linarith only [hh]
  have hsub₂ (a b z : TangentSpace (𝓡 n) x) :
      r x a (b - z) = r x a b - r x a z := by
    have hh := map_sub ((deriv G t) a) b z
    rw [hq, hq, hq] at hh
    linarith only [hh]
  have hsymm (a b : TangentSpace (𝓡 n) x) : r x a b = r x b a := by
    have hb := (he b a).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s => (F.metric s).symm x a b))
    have hh := (he a b).unique hb
    linarith only [hh]
  have hXx := (hX.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hYx := (hY.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hZx := (hZ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  rw [← ((F.connection t).connection.torsion_eq_zero_iff.mp
      (F.connection t).torsion_eq_zero) hXx hYx,
    ← ((F.connection t).connection.torsion_eq_zero_iff.mp
      (F.connection t).torsion_eq_zero) hXx hZx,
    ← ((F.connection t).connection.torsion_eq_zero_iff.mp
      (F.connection t).torsion_eq_zero) hYx hZx,
    hsub₁, hsub₂, hsub₂] at hk
  dsimp only [cr]
  rw [hsymm (Z x) ((F.connection t).connection X x (Y x)),
    hsymm ((F.connection t).connection X x (Z x)) (Y x),
    hsymm ((F.connection t).connection Z x (Y x)) (X x)]
  change _ = _ at hk
  dsimp only [V] at hk
  linarith only [hk]

end PoincareConjecture.Proofs.M03
