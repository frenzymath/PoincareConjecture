import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.Normalization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Endpoint
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow.Splitting

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem roundAncient_scalarCurvature_eq_one_div_one_sub_time
    (F : RicciFlow 2 M (Iic 0))
    (hround : ∀ t ≤ 0, ConstantPositiveSectionalCurvature (F.metric t) (F.connection t))
    (hzero : ∀ x, (F.connection 0).scalarCurvature x = 1)
    (t : ℝ) (ht : t ≤ 0) (x : M) :
    (F.connection t).scalarCurvature x = 1 / (1 - t) := by
  let R : ℝ → ℝ := fun s => (F.connection s).scalarCurvature x
  have hpos (s : ℝ) (hs : s ≤ 0) : 0 < R s := by
    obtain ⟨c, hc, he⟩ := (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp
      (hround s hs)
    change 0 < (F.connection s).scalarCurvature x
    rw [he x]
    exact hc
  have hderiv (s : ℝ) (hs : s < 0) : HasDerivAt R ((R s) ^ 2) s := by
    have he := F.hasDerivAt_scalarCurvature_surface
      (show s ∈ interior (Iic (0 : ℝ)) by simpa only [interior_Iic, mem_Iio] using hs) x
    obtain ⟨c, _, hc⟩ := (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp
      (hround s hs.le)
    have hfun : (F.connection s).scalarCurvature = fun _ => c := funext hc
    have hlap : (F.connection s).laplacian (F.connection s).scalarCurvature x = 0 := by
      rw [hfun]
      simp [LeviCivitaData.laplacian, LeviCivitaData.hessian,
        LeviCivitaData.hessianOnFields, mvfderiv_const]
    simpa only [hlap, zero_add] using he
  have hq (s : ℝ) (hs : s < 0) :
      HasDerivAt ((fun x : ℝ => 1) / R + id) 0 s := by
    have he := ((hasDerivAt_const s (1 : ℝ)).div (hderiv s hs)
      (ne_of_gt (hpos s hs.le))).add (hasDerivAt_id s)
    have hval : (0 * R s - 1 * R s ^ 2) / R s ^ 2 + 1 = 0 := by
      field_simp [ne_of_gt (hpos s hs.le)]
      ring
    rw [hval] at he
    exact he
  have hconst : EqOn ((fun x : ℝ => 1) / R + id)
      (fun _ => 1 / R (-1) + (-1)) (Iio 0) := by
    intro s hs
    exact isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0 : ℝ)).isPreconnected
      (fun z hz => (hq z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hq z hz).deriv) hs (by norm_num)
  have hcont : ContinuousOn ((fun x : ℝ => 1) / R + id) (Iic 0) :=
    (continuousOn_const.div (F.continuousOn_scalarCurvature_ancient_surface x)
      (fun s hs => ne_of_gt (hpos s hs))).add continuousOn_id
  have hext := hconst.of_subset_closure hcont continuousOn_const
    Iio_subset_Iic_self (by rw [closure_Iio])
  have he : 1 / R t + t = 1 := by
    have he0 := hext (show (0 : ℝ) ∈ Iic 0 by simp)
    have he1 := hext ht
    change 1 / (F.connection 0).scalarCurvature x + 0 = _ at he0
    rw [hzero] at he0
    norm_num at he0 he1
    simpa only [one_div] using he1.trans he0.symm
  have hden : 1 - t ≠ 0 := by linarith
  apply (eq_div_iff hden).mpr
  have he' : 1 / R t = 1 - t := by linarith
  have he'' := (div_eq_iff (ne_of_gt (hpos t ht))).mp he'
  nlinarith

theorem roundAncient_inner_eq_one_sub_time_mul
    (F : RicciFlow 2 M (Iic 0))
    (hround : ∀ t ≤ 0, ConstantPositiveSectionalCurvature (F.metric t) (F.connection t))
    (hzero : ∀ x, (F.connection 0).scalarCurvature x = 1)
    (t : ℝ) (ht : t ≤ 0) (x : M) (a b : TangentSpace (𝓡 2) x) :
    (F.metric t).inner x a b = (1 - t) * (F.metric 0).inner x a b := by
  let f : ℝ → ℝ := fun s => (F.metric s).inner x a b
  have hg (s : ℝ) (hs : s < 0) : HasDerivAt f (-f s / (1 - s)) s := by
    have he := (F.equation s hs.le x a b).hasDerivAt (Iic_mem_nhds hs)
    have hric : -2 * (F.connection s).ricci x a b = -f s / (1 - s) := by
      rw [(F.connection s).ricci_eq_half_scalarCurvature_mul_inner,
        roundAncient_scalarCurvature_eq_one_div_one_sub_time F hround hzero s hs.le x]
      dsimp only [f]
      ring
    rwa [hric] at he
  have hq (s : ℝ) (hs : s < 0) :
      HasDerivAt (f / ((fun x : ℝ => 1) - (id : ℝ → ℝ))) 0 s := by
    have hden : 1 - s ≠ 0 := by linarith
    have he := (hg s hs).div ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)) hden
    have hval :
        (-f s / (1 - s) * ((fun x : ℝ => (1 : ℝ)) - (id : ℝ → ℝ)) s - f s * (0 - 1)) /
            ((fun x : ℝ => (1 : ℝ)) - (id : ℝ → ℝ)) s ^ 2 = 0 := by
      simp only [Pi.sub_apply, id_eq]
      field_simp [hden]
      ring
    rw [hval] at he
    exact he
  have hconst : EqOn (f / ((fun x : ℝ => 1) - (id : ℝ → ℝ)))
      (fun _ => f (-1) / (1 - (-1))) (Iio 0) := by
    intro s hs
    exact isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0 : ℝ)).isPreconnected
      (fun z hz => (hq z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hq z hz).deriv) hs (by norm_num)
  have hcont : ContinuousOn (f / ((fun x : ℝ => 1) - (id : ℝ → ℝ))) (Iic 0) :=
    (Poincare.Geometry.RicciFlow.Harnack.metric_inner_contDiffOn_time F x a b).continuousOn.div
      (continuousOn_const.sub continuousOn_id) (fun s hs => by
        change 1 - s ≠ 0
        have hs' : s ≤ 0 := hs
        linarith)
  have hext := hconst.of_subset_closure hcont continuousOn_const
    Iio_subset_Iic_self (by rw [closure_Iio])
  have he : f t / (1 - t) = f 0 := by
    have he0 := hext (show (0 : ℝ) ∈ Iic 0 by simp)
    have he1 := hext ht
    norm_num only [sub_zero, div_one] at he0 he1
    have he1' : f t / (1 - t) = f (-1) / 2 := by
      simpa only [Pi.div_apply, Pi.sub_apply, id_eq] using he1
    have he0' : f (-1) / 2 = f 0 := by
      simpa only [Pi.div_apply, Pi.sub_apply, id_eq, sub_zero, div_one] using he0.symm
    exact he1'.trans he0'
  have hden : 1 - t ≠ 0 := by linarith
  simpa only [mul_comm] using (div_eq_iff hden).mp he

theorem compactRoundAncient_inner_eq_one_sub_time_mul_of_soliton
    [CompactSpace M] (F : RicciFlow 2 M (Iic 0))
    (hround : ∀ t ≤ 0, ConstantPositiveSectionalCurvature (F.metric t) (F.connection t))
    {φ : M → ℝ} (hφ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 φ)
    (hsol : ∀ (x : M) (a b : TangentSpace (𝓡 2) x),
      (F.connection 0).ricci x a b + (F.connection 0).hessian φ x a b =
        (1 / 2 : ℝ) * (F.metric 0).inner x a b)
    (t : ℝ) (ht : t ≤ 0) (x : M) (a b : TangentSpace (𝓡 2) x) :
    (F.metric t).inner x a b = (1 - t) * (F.metric 0).inner x a b := by
  apply roundAncient_inner_eq_one_sub_time_mul F hround ?_ t ht x a b
  intro y
  have he := (F.connection 0).scalar_eq_twice_scale_of_compact_round_soliton
    hφ hsol (hround 0 le_rfl) y
  norm_num at he ⊢
  exact he

end PoincareConjecture.RicciFlow.Splitting
