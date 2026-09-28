import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.Projection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.BallEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem exists_global_extension_near_zero
    {g : E2 → E2} {U : Set E2} (hU : IsOpen U) (hg : ContDiffOn Real ∞ g U)
    (h0 : 0 ∈ U) (hbij : Bijective (fderiv Real g 0)) :
    ∃ r > 0, closedBall (0 : E2) r ⊆ U ∧
      ∃ G : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        ∀ x ∈ closedBall (0 : E2) r, G x = g x := by
  let L := ContinuousLinearEquiv.ofBijective (fderiv Real g 0)
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have hg0 : ContDiffAt Real ∞ g 0 := hg.contDiffAt (hU.mem_nhds h0)
  have hd : HasFDerivAt g L.toContinuousLinearMap 0 :=
    (hg0.differentiableAt (by simp)).hasFDerivAt
  let Q := hg0.toOpenPartialHomeomorph g hd (by simp)
  let V := U ∩ (fderiv Real g) ⁻¹'
    range (fun B : E2 ≃L[Real] E2 => B.toContinuousLinearMap)
  have hV : IsOpen V :=
    (hg.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage hU
      ContinuousLinearEquiv.isOpen
  have h0V : (0 : E2) ∈ V := ⟨h0, L, rfl⟩
  have hloc : IsLocalDiffeomorphOn (𝓡 2) (𝓡 2) ∞ g V := by
    apply Poincare.isLocalDiffeomorphOn_of_contMDiffOn_bijective_mfderiv hV
      (hg.mono inter_subset_left).contMDiffOn
    rintro x ⟨_, B, hB⟩
    rw [mfderiv_eq_fderiv, ← hB]
    exact B.bijective
  have h0Q : (0 : E2) ∈ Q.source := hg0.mem_toOpenPartialHomeomorph_source hd (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hV.inter Q.open_source).mem_nhds ⟨h0V, h0Q⟩)
  obtain ⟨G, hG⟩ := exists_global_extension_of_local_ball_embedding hr g
    (fun x hx y hy hxy => Q.injOn (hball hx).2 (hball hy).2 hxy)
    (fun x hx => hloc ⟨x, (hball hx).1⟩)
  exact ⟨r, hr, fun x hx => (hball hx).1.1, G, hG⟩

private def planarProjection : E3 →L[Real] E2 :=
  LinearMap.toContinuousLinearMap {
    toFun := Saddle.toE2
    map_add' := by intro x y; ext i; fin_cases i <;> simp [Saddle.toE2]
    map_smul' := by intro c x; ext i; fin_cases i <;> simp [Saddle.toE2] }

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem exists_planar_chart_of_critical_height
    (F : S2 → E3) (hF : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F)
    (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => F q 2) p = 0) :
    ∃ r > 0, closedBall (0 : E2) r ⊆ e.source ∧
      ∃ R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        ∀ x ∈ closedBall (0 : E2) r,
          R x = Saddle.toE2 (F (e x)) := by
  subst p
  let c : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 S2 ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := he
    contMDiffOn_invFun := hei }
  have heloc : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ e 0 :=
    ⟨c, he0, fun _ _ => rfl⟩
  let H : E2 → E3 := F ∘ e
  have hH : ContDiffOn Real ∞ H e.source :=
    (hF.contMDiff.comp_contMDiffOn he).contDiffOn
  have hH0 : ContDiffAt Real ∞ H 0 := hH.contDiffAt (e.open_source.mem_nhds he0)
  have hchain : fderiv Real H 0 = (mfderiv (𝓡 2) (𝓡 3) F (e 0)).comp
      (mfderiv (𝓡 2) (𝓡 2) e 0) := by
    have h := mfderiv_comp 0
      ((hF.contMDiff (e 0)).mdifferentiableAt (by simp))
      (heloc.mdifferentiableAt (by simp))
    rwa [mfderiv_eq_fderiv] at h
  have hinj : Injective (fderiv Real H 0) := by
    rw [hchain]
    exact (injective_mfderiv_sphere_embedding hF (e 0)).comp
      (heloc.mfderivToContinuousLinearEquiv (by simp)).injective
  have hzero : (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).comp
      (fderiv Real H 0) = 0 := by
    have h := mfderiv_comp 0
      (((EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contMDiff.comp
        hF.contMDiff) (e 0) |>.mdifferentiableAt
          (by simp)) (heloc.mdifferentiableAt (by simp))
    have hc0 : mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => F q 2) (e 0) = 0 := by
      exact hc
    change mfderiv (𝓡 2) 𝓘(Real, Real)
      ((fun q => F q 2) ∘ e) 0 =
      (mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => F q 2) (e 0)).comp
          (mfderiv (𝓡 2) (𝓡 2) e 0) at h
    rw [hc0, ContinuousLinearMap.zero_comp] at h
    have hd := (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).hasFDerivAt.comp 0
      (hH0.differentiableAt (by simp)).hasFDerivAt
    rw [mfderiv_eq_fderiv] at h
    rw [← hd.fderiv]
    change fderiv Real ((fun q : S2 => F q 2) ∘ e) 0 = 0
    exact h
  have hpder := planarProjection.hasFDerivAt.comp 0
    (hH0.differentiableAt (by simp)).hasFDerivAt
  apply exists_global_extension_near_zero e.open_source
    (planarProjection.contDiff.comp_contDiffOn hH) he0
  rw [hpder.fderiv]
  have hi : Injective (planarProjection.comp (fderiv Real H 0)) := by
    intro u v huv
    apply hinj
    have hz (x : E2) : fderiv Real H 0 x 2 = 0 :=
      congrArg (fun L : E2 →L[Real] Real => L x) hzero
    ext i
    fin_cases i
    · exact congrArg (fun x : E2 => x 0) huv
    · exact congrArg (fun x : E2 => x 1) huv
    · exact (hz u).trans (hz v).symm
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

private theorem embedding_postcompose
    (hg : g ∈ M.tree.leaves) (J : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (J ∘ g) := by
  have hge := M.tree.embedding_of_mem_leaves hg
  apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
    (J.contMDiff.comp hge.contMDiff) (J.injective.comp hge.isEmbedding.injective)
  intro q
  rw [mfderiv_comp q ((J.contMDiff (g q)).mdifferentiableAt (by simp))
    ((hge.contMDiff q).mdifferentiableAt (by simp))]
  exact (J.mfderivToContinuousLinearEquiv (by simp) (g q)).injective.comp
    (injective_mfderiv_sphere_embedding hge q)



theorem exists_terminal_planar_chart
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0) :
    ∃ r > 0, closedBall (0 : E2) r ⊆ e.source ∧
      ∃ R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        ∀ x ∈ closedBall (0 : E2) r,
          R x = Saddle.toE2 (d.flatten (g (e x))) := by
  apply exists_planar_chart_of_critical_height (d.flatten ∘ g)
    (embedding_postcompose hg d.flatten) he0 hep he hei
  have hh : (fun q => d.flatten (g q) 2) =
      (fun q => inner Real (M.v : E3) (g q)) := by
    funext q
    exact (d.frame_height (d.D (g q))).trans (d.D_height (g q))
  change mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => d.flatten (g q) 2) p = 0
  rw [hh]
  exact hc



theorem exists_terminal_planar_chart_before_flattening
    (hg : g ∈ M.tree.leaves)
    (J : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hJ : ∀ y, J y 2 = inner Real (M.v : E3) y)
    (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0) :
    ∃ r > 0, closedBall (0 : E2) r ⊆ e.source ∧
      ∃ R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        ∀ x ∈ closedBall (0 : E2) r, R x = Saddle.toE2 (J (g (e x))) := by
  apply exists_planar_chart_of_critical_height (J ∘ g)
    (embedding_postcompose hg J) he0 hep he hei
  change mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => J (g q) 2) p = 0
  have hh : (fun q => J (g q) 2) = (fun q => inner Real (M.v : E3) (g q)) :=
    funext (fun q => hJ (g q))
  rw [hh]
  exact hc

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
