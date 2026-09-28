import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.JointCoordinateGeodesicEndpoint
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped ContDiff Topology

universe u

namespace PoincareConjecture.M63

theorem exists_joint_coordinate_exponential_inverse
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    {U : Set E} (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hinv : ∀ y ∈ U, (B y).IsInvertible)
    (hsymm : ∀ y ∈ U, ∀ v w, B y v w = B y w v)
    {x : E} (hx : x ∈ U) :
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      (x, 0) ∈ e.source ∧ e (x, 0) = (x, x) ∧
      e.source ⊆ U ×ˢ univ ∧ e.target ⊆ U ×ˢ U ∧
      ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ z ∈ e.source, (e z).1 = z.1) ∧
      ∃ Gamma : (E × E) × ℝ → E × E,
        ContDiffOn ℝ ∞ Gamma (e.source ×ˢ Ioo (-2 : ℝ) 2) ∧
        ∀ z ∈ e.source,
          Gamma (z, 0) = z ∧ (Gamma (z, 1)).1 = (e z).2 ∧
          ∀ t ∈ Ioo (-2 : ℝ) 2,
            (Gamma (z, t)).1 ∈ U ∧
            HasDerivAt (fun s => Gamma (z, s))
              (coordinateGeodesicField B (Gamma (z, t))) t := by
  obtain ⟨epsilon, r, hepsilon, hr, hUball, Gamma, hGamma, hspec, hzero, hend⟩ :=
    exists_joint_coordinate_geodesic_endpoint hU hB hinv hsymm hx
  let D := ball x epsilon ×ˢ ball (0 : E) r
  have hD : IsOpen D := isOpen_ball.prod isOpen_ball
  have hX : (x, (0 : E)) ∈ D := ⟨mem_ball_self hepsilon, mem_ball_self hr⟩
  let A : E × E → E × E := fun z => (z.1, (Gamma (z, 1)).1)
  have htime : ContDiff ℝ ∞ (fun z : E × E => (z, (1 : ℝ))) := by fun_prop
  have hA : ContDiffOn ℝ ∞ A D :=
    contDiffOn_fst.prodMk
      ((hGamma.comp htime.contDiffOn (fun _ hz => ⟨hz, by norm_num⟩)).fst)
  have hAt : ContDiffAt ℝ ∞ A (x, 0) := hA.contDiffAt (hD.mem_nhds hX)
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hder : HasFDerivAt A (fderiv ℝ A (x, 0)) (x, 0) :=
    (hAt.differentiableAt hn).hasFDerivAt
  let S : (E × E) ≃L[ℝ] (E × E) :=
    { toFun := fun z => (z.1, z.1 + z.2)
      invFun := fun z => (z.1, z.2 - z.1)
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp
      map_add' := by intro z w; ext <;> simp [add_add_add_comm]
      map_smul' := by intro c z; ext <;> simp [smul_add]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

  have hleft : (fderiv ℝ A (x, 0)).comp (ContinuousLinearMap.inl ℝ E E) =
      (S : (E × E) →L[ℝ] E × E).comp (ContinuousLinearMap.inl ℝ E E) := by
    have hcomp := hder.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x (0 : E))
    have hpos : HasFDerivAt (fun y : E => A (y, 0))
        ((ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)) x := by
      apply ((hasFDerivAt_id x).prodMk (hasFDerivAt_id x)).congr_of_eventuallyEq
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hepsilon)] with y hy
      dsimp only [A]
      rw [hzero y hy 1 (by norm_num)]
      rfl
    refine (hcomp.unique hpos).trans ?_
    ext y <;> simp [S]
  have hright : (fderiv ℝ A (x, 0)).comp (ContinuousLinearMap.inr ℝ E E) =
      (S : (E × E) →L[ℝ] E × E).comp (ContinuousLinearMap.inr ℝ E E) := by
    have hcomp := hder.comp (0 : E) (hasFDerivAt_prodMk_right (𝕜 := ℝ) x (0 : E))
    have hvel : HasFDerivAt (fun v : E => A (x, v))
        ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) 0 := by
      exact (hasFDerivAt_const x (0 : E)).prodMk (hend x (mem_ball_self hepsilon))
    refine (hcomp.unique hvel).trans ?_
    ext v <;> simp [S]
  have hFS : fderiv ℝ A (x, 0) = (S : (E × E) →L[ℝ] E × E) :=
    ContinuousLinearMap.prod_ext hleft hright
  have hderS : HasFDerivAt A (S : (E × E) →L[ℝ] E × E) (x, 0) := by
    rw [← hFS]
    exact hder
  have hfd : ContinuousAt (fderiv ℝ A) (x, 0) :=
    (hAt.fderiv_right (m := 0) (by simp)).continuousAt
  have hinvertible : {z : E × E | ∃ L : (E × E) ≃L[ℝ] (E × E),
      (L : (E × E) →L[ℝ] E × E) = fderiv ℝ A z} ∈ 𝓝 (x, 0) := by
    have h := S.nhds
    change Set.range (fun L : (E × E) ≃L[ℝ] (E × E) =>
      (L : (E × E) →L[ℝ] E × E)) ∈ 𝓝 (S : (E × E) →L[ℝ] E × E) at h
    rw [← hFS] at h
    exact hfd.preimage_mem_nhds h
  obtain ⟨delta, hdelta, hsub⟩ :=
    Metric.mem_nhds_iff.mp (inter_mem (hD.mem_nhds hX) hinvertible)
  let H := hAt.toOpenPartialHomeomorph A (f' := S) hderS hn
  let e := H.restrOpen (ball (x, (0 : E)) delta) isOpen_ball
  have hsource : e.source ⊆ D := fun z hz => (hsub hz.2).1
  have heq : (e : E × E → E × E) = A := rfl
  have heX : (x, (0 : E)) ∈ e.source :=
    ⟨hAt.mem_toOpenPartialHomeomorph_source hderS hn, mem_ball_self hdelta⟩
  have hezero : e (x, 0) = (x, x) := by
    change (x, (Gamma ((x, 0), 1)).1) = (x, x)
    rw [hzero x (mem_ball_self hepsilon) 1 (by norm_num)]
  have hsourceU : e.source ⊆ U ×ˢ univ :=
    fun z hz => ⟨hUball (hsource hz).1, mem_univ z.2⟩
  have htargetU : e.target ⊆ U ×ˢ U := by
    intro q hq
    have hz := hsource (e.map_target hq)
    have hAz : A (e.symm q) ∈ U ×ˢ U :=
      ⟨hUball hz.1, (hspec _ hz.1 _ hz.2).2 1 (by norm_num) |>.1⟩
    have hqeq : A (e.symm q) = q := e.right_inv hq
    exact hqeq ▸ hAz
  have hesmooth : ContDiffOn ℝ ∞ e e.source := hA.mono hsource
  have heinverse : ContDiffOn ℝ ∞ e.symm e.target := by
    intro q hq
    have hqs := e.map_target hq
    obtain ⟨L, hL⟩ := (hsub hqs.2).2
    have hsmooth : ContDiffAt ℝ ∞ e (e.symm q) :=
      hA.contDiffAt (hD.mem_nhds (hsource hqs))
    have hdiff : HasFDerivAt e (L : (E × E) →L[ℝ] E × E) (e.symm q) := by
      rw [hL]
      exact (hsmooth.differentiableAt hn).hasFDerivAt
    exact (e.contDiffAt_symm hq hdiff hsmooth).contDiffWithinAt
  refine ⟨e, heX, hezero, hsourceU, htargetU, hesmooth, heinverse,
    (fun _ _ => rfl), Gamma, hGamma.mono (Set.prod_mono hsource Subset.rfl), ?_⟩
  intro z hz
  have h := hspec z.1 (hsource hz).1 z.2 (hsource hz).2
  refine ⟨h.1, ?_, h.2⟩
  rw [heq]

end PoincareConjecture.M63
