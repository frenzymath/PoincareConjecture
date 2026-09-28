import PoincareConjecture.Proofs.M03.ScalarCommutator
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Connection.Family





















set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle Manifold Set

universe u

namespace PoincareConjecture.RicciFlow.Local

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem mvfderiv_mlieBracket_eq_commutator
    {U : Set M} (hU : IsOpen U) {f : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (X Y : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    {x : M} (hx : x ∈ U) :
    mvfderiv (𝓡 n) f x (VectorField.mlieBracket (𝓡 n) X Y x) =
      mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y (Y y)) x (X x) -
        mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y (X y)) x (Y x) := by
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let e := extChartAt (𝓡 n) x
  have hex : e.symm (e x) = x := e.left_inv (mem_extChartAt_source x)
  have he0 : e x ∈ e.target := mem_extChartAt_target x
  have he (q : EuclideanSpace ℝ (Fin n)) (hq : q ∈ e.target) :
      ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ e.symm q :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).contMDiffAt
      (extChartAt_target_mem_nhds' hq)
  have hei (q : EuclideanSpace ℝ (Fin n)) (hq : q ∈ e.target) :
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) e.symm q).IsInvertible := by
    simpa only [(𝓡 n).range_eq_univ, mfderivWithin_univ] using
      (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 n) hq)
  have heid : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) e.symm (e x) =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) (e x)) := by
    simpa only [(𝓡 n).range_eq_univ, mfderivWithin_univ] using!
      (mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x))
  have hfx := hf.contMDiffAt (hU.mem_nhds hx)
  have hfex : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (e.symm (e x)) := by
    simpa only [hex] using hfx
  let h : EuclideanSpace ℝ (Fin n) → ℝ := f ∘ e.symm
  let V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun q => VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) e.symm X q
  let W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun q => VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) e.symm Y q
  have hh : ContDiffAt ℝ ∞ h (e x) := (hfex.comp (e x) (he _ he0)).contDiffAt
  have hfield (Z : (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U) :
      ContDiffAt ℝ ∞
        (VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) e.symm Z) (e x) := by
    have hZex : ContMDiffAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) (e.symm (e x)) := by
      simpa only [hex] using hZ.contMDiffAt (hU.mem_nhds hx)
    exact contMDiffAt_vectorSpace_iff_contDiffAt.mp
      (hZex.mpullback_vectorField_preimage (he _ he0) (hei _ he0) (by simp))
  have hdir (Z : (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U) :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => mvfderiv (𝓡 n) f y (Z y)) x := by
    have hd := ContMDiffAt.clm_apply_of_inCoordinates (b₁ := id) (b₂ := f)
      (hfx.mfderiv_const (m := ∞) (n := ∞) (by simp))
      (hZ.contMDiffAt (hU.mem_nhds hx)) hfx
    convert (Bundle.contMDiffAt_totalSpace.mp hd).2 using 1
    funext y
    simp only [trivializationAt_model_space_apply]
    rfl
  have hU' : e.symm ⁻¹' U ∈ 𝓝 (e x) :=
    (he _ he0).continuousAt.preimage_mem_nhds (by simpa only [hex] using hU.mem_nhds hx)
  have htransport (Z : (y : M) → TangentSpace (𝓡 n) y) :
      (fun q => fderiv ℝ h q
        (VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) e.symm Z q))
        =ᶠ[𝓝 (e x)] (fun q => mvfderiv (𝓡 n) f (e.symm q) (Z (e.symm q))) := by
    filter_upwards [hU', extChartAt_target_mem_nhds (I := 𝓡 n) x] with q hqU hq
    have hfd := (hf.contMDiffAt (hU.mem_nhds hqU)).mdifferentiableAt (by simp)
    rw [← mfderiv_eq_fderiv]
    change mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (f ∘ e.symm) q _ = _
    rw [mvfderiv_comp q hfd ((he q hq).mdifferentiableAt (by simp)),
      VectorField.mpullback_apply, ContinuousLinearMap.comp_apply,
      (hei q hq).self_apply_inverse]
  have houter (Z : (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
      (a : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun q => fderiv ℝ h q
        (VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) e.symm Z q))
        (e x) a = mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y (Z y)) x a := by
    rw [(htransport Z).fderiv_eq, ← mfderiv_eq_fderiv]
    change mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ((fun y => mvfderiv (𝓡 n) f y (Z y)) ∘ e.symm) (e x) a = _
    rw [mvfderiv_comp_apply_of_eq (e x) ((hdir Z hZ).mdifferentiableAt (by simp))
      ((he _ he0).mdifferentiableAt (by simp)) hex a, heid]
    rfl
  have hval (Z : (y : M) → TangentSpace (𝓡 n) y) :
      VectorField.mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) e.symm Z (e x) = Z x := by
    have hinv :
        ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) e.symm (e x)).inverse
          (Z (e.symm (e x))) : EuclideanSpace ℝ (Fin n)) = Z (e.symm (e x)) := by
      simpa only [(𝓡 n).range_eq_univ, mfderivWithin_univ] using!
        (mfderivWithin_extChartAt_symm_inverse_apply (I := 𝓡 n)
          (x := x) (Z (e.symm (e x))))
    have hvalue : (Z (e.symm (e x)) : EuclideanSpace ℝ (Fin n)) = Z x :=
      congrArg (fun y => (Z y : EuclideanSpace ℝ (Fin n))) hex
    exact hinv.trans hvalue
  have hdf : fderiv ℝ h (e x) = mvfderiv (𝓡 n) f x := by
    rw [← mfderiv_eq_fderiv]
    change mvfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (f ∘ e.symm) (e x) = _
    rw [mvfderiv_comp (e x) (hfex.mdifferentiableAt (by simp))
      ((he _ he0).mdifferentiableAt (by simp)), heid]
    change mvfderiv (𝓡 n) f (e.symm (e x)) = mvfderiv (𝓡 n) f x
    rw [hex]
  have hbr : VectorField.mlieBracket (𝓡 n) X Y x =
      VectorField.lieBracket ℝ V W (e x) := by
    delta VectorField.mlieBracket
    rw [VectorField.mlieBracketWithin_apply]
    simp only [(𝓡 n).range_eq_univ, Set.preimage_univ, Set.inter_univ,
      VectorField.mpullbackWithin_univ, mfderiv_extChartAt_self]
    change (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).inverse
      (VectorField.lieBracketWithin ℝ V W Set.univ (e x)) = _
    rw [ContinuousLinearMap.inverse_id]
    change VectorField.lieBracketWithin ℝ V W Set.univ (e x) = _
    rw [VectorField.lieBracketWithin_univ]
  have hEuclid := VectorField.fderiv_apply_lieBracket (V := V) (W := W) hh
    (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    ((hfield Y hY).differentiableAt (by simp))
    ((hfield X hX).differentiableAt (by simp))
  have houterY := houter Y hY (V (e x))
  have houterX := houter X hX (W (e x))
  change fderiv ℝ (fun q => fderiv ℝ h q (W q)) (e x) (V (e x)) = _ at houterY
  change fderiv ℝ (fun q => fderiv ℝ h q (V q)) (e x) (W (e x)) = _ at houterX
  rw [houterY, houterX] at hEuclid
  have hV : V (e x) = X x := hval X
  have hW : W (e x) = Y x := hval Y
  rw [hV, hW] at hEuclid
  rw [hbr, ← hdf]
  exact hEuclid

end PoincareConjecture.RicciFlow.Local
