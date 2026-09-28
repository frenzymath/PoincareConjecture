import PoincareConjecture.Proofs.M03.ConnectionCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Connection.Koszul
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology
open Bundle Manifold Set

universe u

namespace PoincareConjecture.RicciFlow.Local

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem contMDiffAt_clm_apply_iff
    [IsManifold (𝓡 n) ∞ M]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ F]
    {f : M → F →L[ℝ] G} {p : M} :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, F →L[ℝ] G) ∞ f p ↔
      ∀ v : F, ContMDiffAt (𝓡 n) 𝓘(ℝ, G) ∞ (fun q ↦ f q v) p := by
  constructor
  · intro h v
    exact h.clm_apply contMDiffAt_const
  · intro h
    let d := Module.finrank ℝ F
    have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
    let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
    let e₂ := (e₁.arrowCongr (ContinuousLinearEquiv.refl ℝ G)).trans
      (ContinuousLinearEquiv.piRing (Fin d))
    have hc : ContMDiffAt (𝓡 n) 𝓘(ℝ, Fin d → G) ∞ (fun q ↦ e₂ (f q)) p := by
      apply contMDiffAt_pi_space.mpr
      intro i
      change ContMDiffAt (𝓡 n) 𝓘(ℝ, G) ∞
        (fun q ↦ f q (e₁.symm (Pi.single i 1))) p
      exact h (e₁.symm (Pi.single i 1))
    have hb := (contMDiffAt_const (c := e₂.symm.toContinuousLinearMap)).clm_apply hc
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using hb

variable [IsManifold (𝓡 n) ∞ M]

theorem contMDiffOn_koszulExpression
    (g : RiemannianMetric n M) {U : Set M} (hU : IsOpen U)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞ (T% Z) U) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x ↦
        mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) +
        mvfderiv (𝓡 n) (fun y ↦ g.inner y (Z y) (X y)) x (Y x) -
        mvfderiv (𝓡 n) (fun y ↦ g.inner y (X y) (Y y)) x (Z x) +
        g.inner x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) -
        g.inner x (Y x) (VectorField.mlieBracket (𝓡 n) X Z x) -
        g.inner x (X x) (VectorField.mlieBracket (𝓡 n) Y Z x)) U := by
  intro x hx
  have hXp := (hX x hx).contMDiffAt (hU.mem_nhds hx)
  have hYp := (hY x hx).contMDiffAt (hU.mem_nhds hx)
  have hZp := (hZ x hx).contMDiffAt (hU.mem_nhds hx)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞)
      (by
        rw [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hXY := hX.inner_bundle hY
  have hZX := hZ.inner_bundle hX
  have hYZ := hY.inner_bundle hZ
  have hXY_at := (hXY x hx).contMDiffAt (hU.mem_nhds hx)
  have hZX_at := (hZX x hx).contMDiffAt (hU.mem_nhds hx)
  have hYZ_at := (hYZ x hx).contMDiffAt (hU.mem_nhds hx)
  have hXdir := ContMDiffAt.clm_apply_of_inCoordinates
    (b₁ := id) (b₂ := fun q ↦ (g.inner q) (Y q) (Z q))
    (hYZ_at.mfderiv_const (m := ∞) (n := ∞) (by simp)) hXp hYZ_at
  have hYdir := ContMDiffAt.clm_apply_of_inCoordinates
    (b₁ := id) (b₂ := fun q ↦ (g.inner q) (Z q) (X q))
    (hZX_at.mfderiv_const (m := ∞) (n := ∞) (by simp)) hYp hZX_at
  have hZdir := ContMDiffAt.clm_apply_of_inCoordinates
    (b₁ := id) (b₂ := fun q ↦ (g.inner q) (X q) (Y q))
    (hXY_at.mfderiv_const (m := ∞) (n := ∞) (by simp)) hZp hXY_at
  have hbrXY := hXp.mlieBracket_vectorField (m := ⊤) (n := ⊤) hYp (by simp)
  have hbrXZ := hXp.mlieBracket_vectorField (m := ⊤) (n := ⊤) hZp (by simp)
  have hbrYZ := hYp.mlieBracket_vectorField (m := ⊤) (n := ⊤) hZp (by simp)
  have hXdir' := (Bundle.contMDiffAt_totalSpace.mp hXdir).2
  have hYdir' := (Bundle.contMDiffAt_totalSpace.mp hYdir).2
  have hZdir' := (Bundle.contMDiffAt_totalSpace.mp hZdir).2
  have hsum := (((((hXdir'.add hYdir').sub hZdir').add
    (hbrXY.inner_bundle hZp)).sub (hYp.inner_bundle hbrXZ)).sub
    (hXp.inner_bundle hbrYZ))
  convert hsum.contMDiffWithinAt using 1
  funext y
  simp only [trivializationAt_model_space_apply, Pi.add_apply]
  rfl

theorem koszul_operator_contMDiffOn
    (g : RiemannianMetric n M)
    (A : (Y : (x : M) → TangentSpace (𝓡 n) x) →
      (x : M) → TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x)
    (hA : ∀ (X Y Z : (x : M) → TangentSpace (𝓡 n) x) {x : M},
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) (T% X) x →
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) (T% Y) x →
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) (T% Z) x →
      g.inner x (A Y x (X x)) (Z x) = (1 / 2 : ℝ) *
        (mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) +
        mvfderiv (𝓡 n) (fun y ↦ g.inner y (Z y) (X y)) x (Y x) -
        mvfderiv (𝓡 n) (fun y ↦ g.inner y (X y) (Y y)) x (Z x) +
        g.inner x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) -
        g.inner x (Y x) (VectorField.mlieBracket (𝓡 n) X Z x) -
        g.inner x (X x) (VectorField.mlieBracket (𝓡 n) Y Z x)))
    {U : Set M} (hU : IsOpen U)
    (Y : (x : M) → TangentSpace (𝓡 n) x)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞ (T% Y) U) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)))) ∞
      (fun x ↦ Bundle.TotalSpace.mk' ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n))) x (A Y x)) U := by
  intro p hp
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have hep : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  let frame (v : (EuclideanSpace ℝ (Fin n))) (q : M) : TangentSpace (𝓡 n) q := e.symmL ℝ q v
  have hframe (v : (EuclideanSpace ℝ (Fin n))) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞
      (T% (frame v)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff (IB := (𝓡 n)) (n := ∞)]
    refine (contMDiffOn_const (c := v)).congr ?_
    intro q hq
    simpa [frame, Trivialization.symmL_apply _ hq] using
      congrArg Prod.snd (e.apply_mk_symm hq v)
  let K (X Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) : ℝ :=
    mvfderiv (𝓡 n) (fun y ↦ g.inner y (Y y) (Z y)) x (X x) +
    mvfderiv (𝓡 n) (fun y ↦ g.inner y (Z y) (X y)) x (Y x) -
    mvfderiv (𝓡 n) (fun y ↦ g.inner y (X y) (Y y)) x (Z x) +
    g.inner x (VectorField.mlieBracket (𝓡 n) X Y x) (Z x) -
    g.inner x (Y x) (VectorField.mlieBracket (𝓡 n) X Z x) -
    g.inner x (X x) (VectorField.mlieBracket (𝓡 n) Y Z x)
  let G (q : M) : (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
      ((EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) (fun x ↦ TangentSpace (𝓡 n) x →L[ℝ] ℝ) p q p q (g.inner q)
  let B (q : M) : (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) :=
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
      p q p q (A Y q)
  have hG : ContMDiffAt (𝓡 n) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) ∞ G p := by
    exact ((contMDiffAt_hom_bundle (fun q ↦
      (TotalSpace.mk' ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) q (g.inner q) :
        TotalSpace ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
          (fun x ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)))).mp
      (g.contMDiff p)).2
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hGinv (q : M) (hq : q ∈ e.baseSet) : (G q).IsInvertible := by
    rw [show G q =
      (e.continuousLinearEquivAt ℝ q hq).arrowCongr (1 : ℝ ≃L[ℝ] ℝ) ∘L
        (g.inner q) ∘L (e.continuousLinearEquivAt ℝ q hq).symm by
      ext a b
      dsimp [G]
      rw [inCoordinates_apply_eq₂ (F₁ := (EuclideanSpace ℝ (Fin n))) (F₂ := (EuclideanSpace ℝ (Fin n))) (F₃ := ℝ)
        (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
        (E₃ := fun _ : M ↦ ℝ) hq hq (by simp)]
      simp [e]
      rfl]
    let : FiniteDimensional ℝ (TangentSpace (𝓡 n) q) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : M → Type _) q
    have hinj : Function.Injective (g.inner q).toLinearMap := by
      intro a b hab
      apply ext_inner_right ℝ
      intro c
      exact congrArg (fun L : TangentSpace (𝓡 n) q →L[ℝ] ℝ ↦ L c) hab
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) q) =
        Module.finrank ℝ (TangentSpace (𝓡 n) q →L[ℝ] ℝ) := by
      calc
        _ = Module.finrank ℝ (Module.Dual ℝ (TangentSpace (𝓡 n) q)) :=
          Subspace.dual_finrank_eq.symm
        _ = _ := (LinearMap.toContinuousLinearMap :
          (TangentSpace (𝓡 n) q →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (TangentSpace (𝓡 n) q →L[ℝ] ℝ)).finrank_eq
    let j : TangentSpace (𝓡 n) q ≃L[ℝ] (TangentSpace (𝓡 n) q →L[ℝ] ℝ) :=
      ((g.inner q).toLinearMap.linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
    have hi : (g.inner q).IsInvertible := by
      rw [show g.inner q = j by
        ext a b
        rfl]
      exact ContinuousLinearMap.isInvertible_equiv
    have hdual : ((e.continuousLinearEquivAt ℝ q hq).arrowCongr
        (1 : ℝ ≃L[ℝ] ℝ) :
        (TangentSpace (𝓡 n) q →L[ℝ] ℝ) →L[ℝ] ((EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)).IsInvertible :=
      ContinuousLinearMap.isInvertible_equiv
    have hT : ((e.continuousLinearEquivAt ℝ q hq).symm :
        (EuclideanSpace ℝ (Fin n)) →L[ℝ] TangentSpace (𝓡 n) q).IsInvertible := ContinuousLinearMap.isInvertible_equiv
    exact hdual.comp (hi.comp hT)
  have hGinv_smooth : ContMDiffAt (𝓡 n) 𝓘(ℝ, ((EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin n))) ∞
      (fun q ↦ ContinuousLinearMap.inverse (G q)) p :=
    (hGinv p hep).contDiffAt_map_inverse.contMDiffAt.comp p hG
  have hB : ContMDiffAt (𝓡 n) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n))) ∞ B p := by
    apply contMDiffAt_clm_apply_iff.mpr
    intro v
    have hQv : ContMDiffAt (𝓡 n) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) ∞
        (fun q ↦ (G q).comp (B q) v) p := by
      apply contMDiffAt_clm_apply_iff.mpr
      intro w
      have hR : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (K (frame v) Y (frame w))
          (U ∩ e.baseSet) :=
        contMDiffOn_koszulExpression g (hU.inter e.open_baseSet)
          (frame v) Y (frame w) ((hframe v).mono inter_subset_right)
          (hY.mono inter_subset_left) ((hframe w).mono inter_subset_right)
      have heq : ∀ᶠ q in 𝓝 p, (G q) (B q v) w =
          (1 / 2 : ℝ) * K (frame v) Y (frame w) q := by
        filter_upwards [hU.mem_nhds hp, e.open_baseSet.mem_nhds hep] with q hq hqe
        have hXq := ((hframe v q hqe).contMDiffAt
          (e.open_baseSet.mem_nhds hqe)).mdifferentiableAt (by simp)
        have hYq := ((hY q hq).contMDiffAt (hU.mem_nhds hq)).mdifferentiableAt (by simp)
        have hZq := ((hframe w q hqe).contMDiffAt
          (e.open_baseSet.mem_nhds hqe)).mdifferentiableAt (by simp)
        rw [show (G q) (B q v) w = g.inner q (A Y q (frame v q)) (frame w q) by
          dsimp [G, B]
          rw [inCoordinates_apply_eq₂ (F₁ := (EuclideanSpace ℝ (Fin n))) (F₂ := (EuclideanSpace ℝ (Fin n))) (F₃ := ℝ)
            (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
            (E₃ := fun _ : M ↦ ℝ) hqe hqe (by simp)]
          rw [ContinuousLinearMap.inCoordinates_eq hqe hqe]
          simp only [Trivial.fiberBundle_trivializationAt',
            Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
            ContinuousLinearMap.comp_apply]
          have hcancel (z : TangentSpace (𝓡 n) q) :
              e.symmL ℝ q ((e.continuousLinearEquivAt ℝ q hqe) z) = z := by
            rw [← e.symm_continuousLinearEquivAt_eq' hqe]
            exact (e.continuousLinearEquivAt ℝ q hqe).symm_apply_apply z
          rw [← Trivialization.symmL_apply (R := ℝ) e hqe]
          rw [Trivialization.symm_continuousLinearEquivAt_eq' (R := ℝ) e hqe]
          change g.inner q (e.symmL ℝ q ((e.continuousLinearEquivAt ℝ q hqe)
            (A Y q (e.symmL ℝ q v)))) (e.symm q w) = _
          rw [hcancel]
          rw [← Trivialization.symmL_apply (R := ℝ) e hqe w]]
        exact hA _ _ _ hXq hYq hZq
      have hhalf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M ↦ (1 / 2 : ℝ)) p :=
        contMDiffAt_const
      have hscalar := (hhalf.smul
        ((hR p ⟨hp, hep⟩).contMDiffAt
          ((hU.inter e.open_baseSet).mem_nhds ⟨hp, hep⟩))).congr_of_eventuallyEq heq
      simpa only [ContinuousLinearMap.comp_apply] using hscalar
    have hBv := hGinv_smooth.clm_apply hQv
    have heq : ∀ᶠ q in 𝓝 p,
        (ContinuousLinearMap.inverse (G q)) ((G q).comp (B q) v) = B q v := by
      filter_upwards [e.open_baseSet.mem_nhds hep] with q hq
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
        congrArg (fun L : (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) ↦ L (B q v))
          (ContinuousLinearMap.IsInvertible.inverse_comp_self (hGinv q hq))
    exact hBv.congr_of_eventuallyEq (Filter.EventuallyEq.symm heq)
  have htotal := (contMDiffAt_hom_bundle (fun q ↦
    (TotalSpace.mk' ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n))) q (A Y q) :
      TotalSpace ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n))) (fun x ↦ TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x)))).mpr
        ⟨contMDiffAt_id, hB⟩
  exact htotal.contMDiffWithinAt

end PoincareConjecture.RicciFlow.Local
