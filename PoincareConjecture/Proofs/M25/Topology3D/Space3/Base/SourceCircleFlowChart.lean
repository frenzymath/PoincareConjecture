import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceTubeChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubePrimitives
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_source_circle_flow_chart
    (P : ℝ × UnitTwoSphere → UnitTwoSphere)
    (hP : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ P)
    (hPzero : ∀ p : UnitTwoSphere, P (0, p) = p)
    (hPadd : ∀ s t : ℝ, ∀ p : UnitTwoSphere, P (s, P (t, p)) = P (s + t, p))
    (f : UnitTwoSphere → ℝ) (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (U : Set UnitTwoSphere) (hU : IsOpen U)
    (hPderiv : ∀ t : ℝ, ∀ p : UnitTwoSphere, P (t, p) ∈ U →
      HasDerivAt (fun s : ℝ => f (P (s, p))) 1 t)
    (a z : ℝ) (haz : a ≤ z)
    (q : UnitCircle → UnitTwoSphere)
    (hq : ContMDiff (𝓡 1) (𝓡 2) ∞ q ∧ Function.Injective q ∧
      ∀ theta : UnitCircle,
        Function.Injective (mfderiv (𝓡 1) (𝓡 2) q theta))
    (hqheight : ∀ theta : UnitCircle, f (q theta) = z)
    (hclosed : ∀ theta : UnitCircle, ∀ t ∈ Icc a z, P (t - z, q theta) ∈ U) :
    ∃ eta : ℝ, 0 < eta ∧
      ∃ e : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere,
        e.source = (univ : Set UnitCircle) ×ˢ Ioo (a - eta) (z + eta) ∧
        ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target ∧
        (∀ p : UnitCircle × ℝ, e p = P (p.2 - z, q p.1)) ∧
        ∀ p ∈ e.source, f (e p) = p.2 := by
  let v : UnitCircle × ℝ → UnitTwoSphere := fun p => P (p.2 - z, q p.1)
  have hv : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ v :=
    hP.comp ((contMDiff_snd.sub contMDiff_const).prodMk
      (hq.1.comp contMDiff_fst))
  obtain ⟨eta, heta, hbuffer⟩ := exists_saddle_end_circle_buffer
    (v ⁻¹' U) (hU.preimage hv.continuous) a z haz (by
      rintro ⟨theta, t⟩ ⟨_, ht⟩
      exact hclosed theta t ht)
  let J := Ioo (a - eta) (z + eta)
  have hzbuffer : z ∈ Icc (a - eta) (z + eta) := by
    constructor <;> linarith
  have hheight (theta : UnitCircle) (t : ℝ)
      (ht : t ∈ Icc (a - eta) (z + eta)) : f (v (theta, t)) = t := by
    have hd (s : ℝ) (hs : s ∈ Icc (a - eta) (z + eta)) :
        HasDerivAt (fun r : ℝ => f (v (theta, r)) - r) 0 s := by
      have hh := ((hPderiv (s - z) (q theta)
        (hbuffer (show (theta, s) ∈ univ ×ˢ Icc (a - eta) (z + eta) from
          ⟨mem_univ _, hs⟩))).comp s
          ((hasDerivAt_id s).sub_const z)).sub (hasDerivAt_id s)
      convert hh using 1 <;> first | rfl | norm_num
    have hzero : ‖(f (v (theta, t)) - t) -
        (f (v (theta, z)) - z)‖ ≤ 0 := by
      have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun s hs => (hd s hs).hasDerivWithinAt)
        (fun _ _ => show ‖(0 : ℝ)‖ ≤ 0 by simp)
        (convex_Icc (a - eta) (z + eta)) hzbuffer ht
      simpa only [zero_mul] using hh
    have heq := sub_eq_zero.mp (norm_le_zero_iff.mp hzero)
    have htop : f (v (theta, z)) = z := by
      simp only [v, sub_self, hPzero, hqheight]
    linarith
  have hheightOpen (p : UnitCircle × ℝ) (hp : p ∈ univ ×ˢ J) :
      f (v p) = p.2 := hheight p.1 p.2 ⟨hp.2.1.le, hp.2.2.le⟩
  have hinj : InjOn v (univ ×ˢ J) := by
    rintro ⟨theta, t⟩ ht ⟨phi, s⟩ hs heq
    have hts : t = s := (hheightOpen _ ht).symm.trans
      ((congrArg f heq).trans (hheightOpen _ hs))
    subst s
    have htzero : z - t + (t - z) = 0 := by ring
    have hh := congrArg (fun y => P (z - t, y)) heq
    simp only [v, hPadd, htzero, hPzero] at hh
    exact Prod.ext (hq.2.1 hh) rfl
  have hderiv (p : UnitCircle × ℝ) (hp : p ∈ univ ×ˢ J) :
      Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) v p) := by
    let A : (TangentSpace (𝓡 1) p.1 × ℝ) →L[ℝ] E2 :=
      mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) v p
    have hnear : f ∘ v =ᶠ[𝓝 p] (Prod.snd : UnitCircle × ℝ → ℝ) := by
      filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds hp] with r hr
      exact hheightOpen r hr
    have hchain := mfderiv_comp p (hf.mdifferentiable (by simp) (v p))
      (hv.mdifferentiable (by simp) p)
    rw [hnear.mfderiv_eq, mfderiv_snd] at hchain
    let slice : UnitCircle → UnitTwoSphere := fun theta => v (theta, p.2)
    let back : UnitTwoSphere → UnitTwoSphere := fun y => P (z - p.2, y)
    have hsmooth : ContMDiff (𝓡 1) (𝓡 2) ∞ slice :=
      hv.comp (contMDiff_id.prodMk contMDiff_const)
    have hback : ContMDiff (𝓡 2) (𝓡 2) ∞ back :=
      hP.comp (contMDiff_const.prodMk contMDiff_id)
    have hrec : back ∘ slice = q := by
      funext theta
      change P (z - p.2, P (p.2 - z, q theta)) = q theta
      rw [hPadd, show z - p.2 + (p.2 - z) = 0 by ring, hPzero]
    have hsliceinj : Injective (mfderiv (𝓡 1) (𝓡 2) slice p.1) := by
      have hh := mfderiv_comp p.1
        (hback.mdifferentiable (by simp) (slice p.1))
        (hsmooth.mdifferentiable (by simp) p.1)
      rw [hrec] at hh
      intro w w' hww
      apply hq.2.2 p.1
      rw [hh]
      exact congrArg (mfderiv (𝓡 2) (𝓡 2) back (slice p.1)) hww
    have hsliceder (w : TangentSpace (𝓡 1) p.1) :
        A (w, 0) = mfderiv (𝓡 1) (𝓡 2) slice p.1 w := by
      have hh := mfderiv_comp p.1 (hv.mdifferentiable (by simp) p)
        (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
      dsimp only [id_eq] at hh
      rw [mfderiv_prod_left] at hh
      exact congrArg (fun L => L w) hh.symm
    apply (injective_iff_map_eq_zero A).mpr
    rintro ⟨w, s⟩ hw
    have hs : s = 0 := by
      have hh := congrArg (fun L => L (w, s)) hchain
      change s = mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (v p) (A (w, s)) at hh
      rw [hw] at hh
      exact hh.trans (map_zero _)
    subst s
    apply Prod.ext
    · apply hsliceinj
      change mfderiv (𝓡 1) (𝓡 2) slice p.1 w =
        mfderiv (𝓡 1) (𝓡 2) slice p.1 0
      exact ((hsliceder w).symm.trans hw).trans (map_zero _).symm
    · rfl
  let : ChartedSpace (EuclideanSpace ℝ (Fin 1) × ℝ) (UnitCircle × ℝ) :=
    prodChartedSpace (EuclideanSpace ℝ (Fin 1)) UnitCircle ℝ ℝ
  let : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × ℝ) ∞ (UnitCircle × ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod UnitCircle ℝ
  have : Nonempty UnitCircle :=
    (NormedSpace.sphere_nonempty (E := E2) (x := 0) |>.mpr zero_le_one).coe_sort
  have hv' : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × ℝ) (𝓡 2) ∞ v
      (univ ×ˢ J) := by
    rw [modelWithCornersSelf_prod]
    exact hv.contMDiffOn
  have hb (p : UnitCircle × ℝ) (hp : p ∈ (univ : Set UnitCircle) ×ˢ J) :
      Bijective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × ℝ) (𝓡 2) v p) := by
    have hi : Injective
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × ℝ) (𝓡 2) v p) := by
      change Injective (fun w : EuclideanSpace ℝ (Fin 1) × ℝ =>
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × ℝ) (𝓡 2) v p w)
      rw [modelWithCornersSelf_prod]
      exact hderiv p hp
    let A : (EuclideanSpace ℝ (Fin 1) × ℝ) →L[ℝ] E2 :=
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × ℝ) (𝓡 2) v p
    exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := A.toLinearMap) (by simp [E2, Module.finrank_prod])).mp hi⟩
  let e := manifoldPatchChart v (isOpen_univ.prod isOpen_Ioo) hv' hb hinj
  have hei := manifoldPatchChart_symm_contMDiffOn v
    (isOpen_univ.prod isOpen_Ioo) hv' hb hinj
  rw [modelWithCornersSelf_prod] at hei
  exact ⟨eta, heta, e, rfl, hv.contMDiffOn, hei,
    fun _ => rfl, hheightOpen⟩

end PoincareConjecture.M25.Topology3D
