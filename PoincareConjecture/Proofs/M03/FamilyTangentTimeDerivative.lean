import PoincareConjecture.Proofs.M03.ConnectionFamily










set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem family_tangent_time_derivative
    (g0 : RiemannianMetric n M)
    {J : Set ℝ} {U : Set M} (hU : IsOpen U)
    (V : ℝ → (x : M) → TangentSpace (𝓡 n) x)
    (hV : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) p.2 (V p.1 p.2)) (J ×ˢ U))
    {t : ℝ} (ht : t ∈ interior J) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g0.toRiemannianMetric⟩
    let dotV := fun x => deriv (fun s => V s x) t
    (∀ x ∈ U, HasDerivAt (fun s => V s x) (dotV x) t) ∧
      ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun x => Bundle.TotalSpace.mk'
          (EuclideanSpace ℝ (Fin n)) x (dotV x)) U := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g0.toRiemannianMetric⟩
  let dotV := fun x => deriv (fun s => V s x) t
  have hV' := hV.mono (show interior J ×ˢ U ⊆ J ×ˢ U from
    fun _ hp => ⟨interior_subset hp.1, hp.2⟩)
  have hderiv : ∀ x ∈ U, HasDerivAt (fun s => V s x) (dotV x) t := by
    intro x hx
    have hAt := (hV' (t, x) ⟨ht, hx⟩).contMDiffAt
      ((isOpen_interior.prod hU).mem_nhds ⟨ht, hx⟩)
    have hi : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun s : ℝ => (s, x)) t := contMDiffAt_id.prodMk contMDiffAt_const
    have hcurve := hAt.comp t hi
    let e := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) x
    have he : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    let L := e.continuousLinearEquivAt ℝ x he
    have hcoord : ContDiffAt ℝ ∞ (fun s => L (V s x)) t := by
      have hc := (Bundle.contMDiffAt_totalSpace.mp hcurve).2.contDiffAt
      change ContDiffAt ℝ ∞ (fun s => L (V s x)) t
      exact hc
    have hactual := L.symm.contDiff.contDiffAt.comp t hcoord
    have hactual' : ContDiffAt ℝ ∞ (fun s => V s x) t := by
      simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hactual
    exact (hactual'.differentiableAt (by simp)).hasDerivAt
  refine ⟨hderiv, ?_⟩
  intro x hx
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) x
  have he : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hVAt := (hV' (t, x) ⟨ht, hx⟩).contMDiffAt
    ((isOpen_interior.prod hU).mem_nhds ⟨ht, hx⟩)
  let C : ℝ × M → EuclideanSpace ℝ (Fin n) := fun q =>
    (e (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q.2 (V q.1 q.2))).2
  have hCAt : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ C (t, x) := by
    have hh := (Bundle.contMDiffAt_totalSpace.mp hVAt).2
    simpa only [C, e] using hh
  let S : M → ℝ → EuclideanSpace ℝ (Fin n) := fun y s => C (s, y)
  have hswap : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (Function.uncurry S) (x, t) :=
    hCAt.comp (x, t) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have hpartial := ContMDiffAt.mfderiv (m := ∞) (n := ∞)
    (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (M := ℝ) (M' := EuclideanSpace ℝ (Fin n)) (J := 𝓡 n)
    S (fun _ : M => t) hswap contMDiffAt_const (by simp)
  erw [inTangentCoordinates_model_space (I := 𝓘(ℝ, ℝ))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))] at hpartial
  have hcoordDeriv : ContMDiffAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun y => deriv (fun s => C (s, y)) t) x := by
    have hh := hpartial.clm_apply (contMDiffAt_const (c := (1 : ℝ)))
    simpa only [mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using hh
  have hcoordDot : ContMDiffAt (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun y => (e (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (dotV y))).2) x := by
    apply hcoordDeriv.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx, e.open_baseSet.mem_nhds he] with y hyU hye
    let L := e.continuousLinearEquivAt ℝ y hye
    have hd := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hderiv y hyU)
    exact hd.deriv.symm
  exact ((Bundle.contMDiffAt_section x).mpr hcoordDot).contMDiffWithinAt

end PoincareConjecture.Proofs.M03
