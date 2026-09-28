import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76


theorem exists_plane_linear_coordinates
    (A : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) (hA : A ≠ 0) :
    ∃ (a : (ℝ × ℝ) →L[ℝ] (Fin 3 → ℝ)) (r : (Fin 3 → ℝ) →L[ℝ] (ℝ × ℝ)),
      Function.LeftInverse r a ∧ LeftInvOn a r {x | A x = 0} ∧ ∀ z,A (a z) = 0 := by
  classical
  have hdim : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ A.ker := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hA
    norm_num at h ⊢
    omega
  let p : (ℝ × ℝ) ≃ₗ[ℝ] A.ker := LinearEquiv.ofFinrankEq _ _ hdim
  let a : (ℝ × ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := A.ker.subtype.comp p.toLinearMap
  have hai : Function.Injective a := Subtype.val_injective.comp p.injective
  obtain ⟨r,hr⟩ := a.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hai)
  have hra : Function.LeftInverse r a := fun z => LinearMap.congr_fun hr z
  refine ⟨a.toContinuousLinearMap,r.toContinuousLinearMap,hra,?_,?_⟩
  · intro x hx
    let z : A.ker := ⟨x,hx⟩
    have hz : a (p.symm z) = x := by change (p (p.symm z) : Fin 3 → ℝ) = x; simp [z]
    change a (r x) = x
    rw [←hz,hra]
  · intro z
    exact (p z).property


theorem exists_convex_intrinsic_loop_chart_with_value
    {X : Type*} [TopologicalSpace X] {F L : Set X}
    (H : OpenPartialHomeomorph X (Fin 3 → ℝ))
    (ell psi : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ) (u v : Fin 3 → ℝ)
    (hellu : ell.contLinear u = 0) (hpsiu : psi.contLinear u = 1)
    (hellv : ell.contLinear v = 1)
    (hF : ∀ y ∈ H.source,y ∈ F ↔ ell (H y) = 0)
    (hL : ∀ y ∈ H.source,y ∈ L ↔ ell (H y) = 0 ∧ psi (H y) = 0)
    (x : F) (hx : (x : X) ∈ H.source) (hHx : H x = 0) (hxL : (x : X) ∈ L) :
    ∃ (q : OpenPartialHomeomorph F (ℝ × ℝ))
      (a : (ℝ × ℝ) →L[ℝ] (Fin 3 → ℝ)) (r : (Fin 3 → ℝ) →L[ℝ] (ℝ × ℝ))
      (m : (ℝ × ℝ) →L[ℝ] ℝ) (w : ℝ × ℝ) (ε : ℝ),
      0 < ε ∧ x ∈ q.source ∧ q.source ⊆ Subtype.val ⁻¹' H.source ∧
      q x = 0 ∧ q.target = ball 0 ε ∧ Convex ℝ q.target ∧
      Function.LeftInverse r a ∧ m w = 1 ∧
      (∀ y : F,q y = r (H y)) ∧
      (∀ z ∈ q.target,(q.symm z : X) = H.symm (a z)) ∧
      (∀ y ∈ q.source,(y : X) ∈ L ↔ m (q y) = 0) ∧
      ∀ y ∈ q.source,m (q y) = psi (H y) := by
  have hell0 : ell 0 = 0 := by simpa only [hHx] using (hF x hx).mp x.property
  have hpsi0 : psi 0 = 0 := by simpa only [hHx] using ((hL x hx).mp hxL).2
  have hell (z : Fin 3 → ℝ) : ell z = ell.contLinear z := by
    have h := ell.toAffineMap.linearMap_vsub z 0
    change ell.contLinear (z-0) = ell z - ell 0 at h
    simpa only [vsub_eq_sub,sub_zero,hell0] using h.symm
  have hpsi (z : Fin 3 → ℝ) : psi z = psi.contLinear z := by
    have h := psi.toAffineMap.linearMap_vsub z 0
    change psi.contLinear (z-0) = psi z - psi 0 at h
    simpa only [vsub_eq_sub,sub_zero,hpsi0] using h.symm
  have hA : ell.contLinear.toLinearMap ≠ 0 := by
    intro h
    have hv := congrArg (fun k : (Fin 3 → ℝ) →ₗ[ℝ] ℝ => k v) h
    exact one_ne_zero (hellv.symm.trans hv)
  obtain ⟨a,r,hra,har,ha0⟩ := exists_plane_linear_coordinates ell.contLinear.toLinearMap hA
  have himage : H.IsImage F {z | ell z = 0} := fun {y} hy => (hF y hy).symm
  obtain ⟨q,hqs,hqt,hqf,hqi⟩ := H.exists_affine_hypersurface_chart ell himage
    a.toContinuousAffineMap r.toContinuousAffineMap hra
    (fun z hz => har (by change ell z = 0 at hz; change ell.contLinear z = 0; rwa [hell] at hz))
    (fun z => by rw [hell]; exact ha0 z) x
  have hxq : x ∈ q.source := hqs.symm.subset hx
  have hqx : q x = 0 := by rw [hqf,hHx]; exact map_zero r
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp q.open_target 0 (hqx ▸ q.map_source hxq)
  let Q := (q.symm.restrOpen (ball 0 ε) isOpen_ball).symm
  have hQt : Q.target = ball 0 ε := by
    change q.target ∩ ball 0 ε = ball 0 ε
    exact inter_eq_right.mpr hball
  have hQs : Q.source = q.source ∩ q ⁻¹' ball 0 ε := by rfl
  let m := psi.contLinear.comp a
  have hvalue : ∀ y ∈ Q.source,m (Q y) = psi (H y) := by
    intro y hy
    have hyH := hqs.subset (hQs.subset hy).1
    have hy0 : ell.contLinear (H y) = 0 := by rw [←hell]; exact (hF y hyH).mp y.property
    change psi.contLinear (a (q y)) = psi (H y)
    rw [hqf]
    change psi.contLinear (a (r (H y))) = psi (H y)
    rw [har hy0,hpsi]
  refine ⟨Q,a,r,m,r u,ε,hε,?_,?_,?_,hQt,?_,hra,?_,?_,?_,?_,hvalue⟩
  · rw [hQs]
    exact ⟨hxq,by change q x ∈ ball 0 ε; rw [hqx]; exact mem_ball_self hε⟩
  · intro y hy
    exact hqs.subset (hQs.subset hy).1
  · exact hqx
  · rw [hQt]
    exact convex_ball 0 ε
  · change psi.contLinear (a (r u)) = 1
    rw [har hellu]
    exact hpsiu
  · exact hqf
  · intro z hz
    exact hqi z (hball (hQt.subset hz))
  · intro y hy
    have hyq := (hQs.subset hy).1
    have hyH := hqs.subset hyq
    have hy0 : ell.contLinear (H y) = 0 := by rw [←hell]; exact (hF y hyH).mp y.property
    change (y : X) ∈ L ↔ psi.contLinear (a (q y)) = 0
    rw [hqf]
    change (y : X) ∈ L ↔ psi.contLinear (a (r (H y))) = 0
    rw [har hy0,←hpsi,hL y hyH,and_iff_right ((hF y hyH).mp y.property)]


theorem exists_convex_intrinsic_loop_chart
    {X : Type*} [TopologicalSpace X] {F L : Set X}
    (H : OpenPartialHomeomorph X (Fin 3 → ℝ))
    (ell psi : (Fin 3 → ℝ) →ᴬ[ℝ] ℝ) (u v : Fin 3 → ℝ)
    (hellu : ell.contLinear u = 0) (hpsiu : psi.contLinear u = 1)
    (hellv : ell.contLinear v = 1)
    (hF : ∀ y ∈ H.source,y ∈ F ↔ ell (H y) = 0)
    (hL : ∀ y ∈ H.source,y ∈ L ↔ ell (H y) = 0 ∧ psi (H y) = 0)
    (x : F) (hx : (x : X) ∈ H.source) (hHx : H x = 0) (hxL : (x : X) ∈ L) :
    ∃ (q : OpenPartialHomeomorph F (ℝ × ℝ))
      (a : (ℝ × ℝ) →L[ℝ] (Fin 3 → ℝ)) (r : (Fin 3 → ℝ) →L[ℝ] (ℝ × ℝ))
      (m : (ℝ × ℝ) →L[ℝ] ℝ) (w : ℝ × ℝ) (ε : ℝ),
      0 < ε ∧ x ∈ q.source ∧ q.source ⊆ Subtype.val ⁻¹' H.source ∧
      q x = 0 ∧ q.target = ball 0 ε ∧ Convex ℝ q.target ∧
      Function.LeftInverse r a ∧ m w = 1 ∧
      (∀ y : F,q y = r (H y)) ∧
      (∀ z ∈ q.target,(q.symm z : X) = H.symm (a z)) ∧
      ∀ y ∈ q.source,(y : X) ∈ L ↔ m (q y) = 0 := by
  obtain ⟨q,a,r,m,w,ε,hε,hxq,hqs,hq0,hqt,hqcv,hra,hmw,hqf,hqi,hLq,_⟩ :=
    exists_convex_intrinsic_loop_chart_with_value H ell psi u v hellu hpsiu hellv hF hL x hx hHx hxL
  exact ⟨q,a,r,m,w,ε,hε,hxq,hqs,hq0,hqt,hqcv,hra,hmw,hqf,hqi,hLq⟩

end PoincareConjecture.M76
