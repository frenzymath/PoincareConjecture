import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Tactic








set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_mvfderiv_time
    {J : Set ℝ} {U : Set M} {f : ℝ × M → ℝ} {h : M → ℝ} {t : ℝ} {x : M}
    (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f (J ×ˢ U))
    (ht : t ∈ interior J) (hx : x ∈ U)
    (htime : ∀ y ∈ U, HasDerivAt (fun s ↦ f (s, y)) (h y) t)
    (v : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s ↦ mvfderiv (𝓡 n) (fun y ↦ f (s, y)) x v)
      (mvfderiv (𝓡 n) h x v) t := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := extChartAt (𝓡 n) x
  let z := e x
  have hex : e.symm z = x := e.left_inv (mem_extChartAt_source x)
  have heU : e.symm ⁻¹' U ∈ 𝓝 z := by
    apply (continuousAt_extChartAt_symm x).preimage_mem_nhds
    change U ∈ 𝓝 (e.symm z)
    rw [hex]
    exact hU.mem_nhds hx
  obtain ⟨W, hWsub, hW, hzW⟩ := mem_nhds_iff.mp
    (inter_mem (extChartAt_target_mem_nhds (I := 𝓡 n) x) heU)
  let S := interior J ×ˢ W
  have hS : IsOpen S := isOpen_interior.prod hW
  have heSmooth : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ e.symm W :=
    (contMDiffOn_extChartAt_symm x).mono fun _ hq ↦ (hWsub hq).1
  let G : ℝ × E → ℝ := fun p ↦ f (p.1, e.symm p.2)
  let k : E → ℝ := fun q ↦ h (e.symm q)
  have hmap : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞ (fun p : ℝ × E ↦ (p.1, e.symm p.2)) S :=
    contMDiffOn_fst.prodMk (heSmooth.comp contMDiffOn_snd (fun _ hp ↦ hp.2))
  have hGm := hf.comp hmap
    (show MapsTo (fun p : ℝ × E ↦ (p.1, e.symm p.2)) S (J ×ˢ U) from
      fun _ hp ↦ ⟨interior_subset hp.1, (hWsub hp.2).2⟩)
  have hG : ContDiffOn ℝ ∞ G S := by
    rw [← contMDiffOn_iff_contDiffOn]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hGm
  have hG2 (s : ℝ) (q : E) (hs : s ∈ interior J) (hq : q ∈ W) :
      ContDiffAt ℝ 2 G (s, q) :=
    (contDiffOn_infty.mp hG 2).contDiffAt (hS.mem_nhds ⟨hs, hq⟩)
  have hD : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) (t, z)) (t, z) :=
    (((hG2 t z ht hzW).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hkeq : k =ᶠ[𝓝 z] fun q ↦ fderiv ℝ G (t, q) ((1 : ℝ), (0 : E)) := by
    filter_upwards [hW.mem_nhds hzW] with q hq
    have hline : HasDerivAt (fun s : ℝ ↦ (s, q)) ((1 : ℝ), (0 : E)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t q)
    have hjoint := ((hG2 t q ht hq).differentiableAt (by norm_num)).hasFDerivAt
    have hd : HasDerivAt (fun s ↦ G (s, q))
        (fderiv ℝ G (t, q) ((1 : ℝ), (0 : E))) t := by
      simpa only [Function.comp_apply] using! hjoint.comp_hasDerivAt t hline
    exact (htime (e.symm q) (hWsub hq).2).unique hd
  have hspace : HasFDerivAt (fun q : E ↦ (t, q))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) z :=
    (hasFDerivAt_const t z).prodMk (hasFDerivAt_id z)
  have hkJoint := (hD.comp z hspace).clm_apply
    (hasFDerivAt_const ((1 : ℝ), (0 : E)) z)
  have hk : DifferentiableAt ℝ k z :=
    hkJoint.differentiableAt.congr_of_eventuallyEq hkeq
  have hkval : fderiv ℝ k z v =
      fderiv ℝ (fderiv ℝ G) (t, z) ((0 : ℝ), v) ((1 : ℝ), (0 : E)) := by
    rw [hkeq.fderiv_eq]
    have heq := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hkJoint.fderiv
    simpa only [Function.comp_apply, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.prod_apply, zero_apply,
      ContinuousLinearMap.id_apply, zero_add, map_zero] using! heq
  have hline : HasDerivAt (fun s : ℝ ↦ (s, z)) ((1 : ℝ), (0 : E)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
  have hdJoint := (hD.comp_hasDerivAt t hline).clm_apply
    (hasDerivAt_const t (((0 : ℝ), v) : ℝ × E))
  have hdTime : HasDerivAt (fun s ↦ fderiv ℝ G (s, z) ((0 : ℝ), v))
      (fderiv ℝ k z v) t := by
    have hsym := ((hG2 t z ht hzW).isSymmSndFDerivAt (by norm_num)).eq
      ((1 : ℝ), (0 : E)) ((0 : ℝ), v)
    apply hdJoint.congr_deriv
    simpa only [map_zero, add_zero, hkval] using hsym
  have hsliceEq : (fun s ↦ fderiv ℝ (fun q : E ↦ G (s, q)) z v) =ᶠ[𝓝 t]
      (fun s ↦ fderiv ℝ G (s, z) ((0 : ℝ), v)) := by
    filter_upwards [isOpen_interior.mem_nhds ht] with s hs
    have hembed : HasFDerivAt (fun q : E ↦ (s, q))
        ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) z :=
      (hasFDerivAt_const s z).prodMk (hasFDerivAt_id z)
    have hcomp := ((hG2 s z hs hzW).differentiableAt (by norm_num)).hasFDerivAt.comp z hembed
    have heq := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hcomp.fderiv
    simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, zero_apply,
      ContinuousLinearMap.id_apply] using! heq
  have hdSlice := hdTime.congr_of_eventuallyEq hsliceEq
  let : IsManifold (𝓡 n) 1 M := IsManifold.of_le (n := ∞)
    (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  have hh : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) h x := by
    rw [← mdifferentiableWithinAt_univ]
    apply DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm
    simpa only [preimage_univ, ModelWithCorners.range_eq_univ, inter_univ,
      differentiableWithinAt_univ] using! hk
  have hchart {a : M → ℝ} (ha : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) a x) :
      mvfderiv (𝓡 n) a x = fderiv ℝ (fun q : E ↦ a (e.symm q)) z := by
    simpa [writtenInExtChartAt, extChartAt_model_space_eq_id, e, z,
      ModelWithCorners.range_eq_univ] using! ha.mvfderiv
  have htimeEq : (fun s ↦ mvfderiv (𝓡 n) (fun y ↦ f (s, y)) x v) =ᶠ[𝓝 t]
      (fun s ↦ fderiv ℝ (fun q : E ↦ G (s, q)) z v) := by
    filter_upwards [isOpen_interior.mem_nhds ht] with s hs
    have hsm : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M ↦ (s, y)) U := contMDiffOn_const.prodMk contMDiffOn_id
    have hsf := hf.comp hsm
      (show MapsTo (fun y : M ↦ (s, y)) U (J ×ˢ U) from
        fun _ hy ↦ ⟨interior_subset hs, hy⟩)
    have hdiff := (hsf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
    have heq := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) (hchart hdiff)
    simpa only [Function.comp_apply, G] using! heq
  have hvalue : fderiv ℝ k z v = mvfderiv (𝓡 n) h x v := by
    have heq := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) (hchart hh)
    simpa only [k] using! heq.symm
  exact (hdSlice.congr_deriv hvalue).congr_of_eventuallyEq htimeEq

end PoincareConjecture.M04

