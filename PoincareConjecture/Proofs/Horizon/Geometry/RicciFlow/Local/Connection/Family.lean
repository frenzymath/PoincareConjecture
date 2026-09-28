import PoincareConjecture.Proofs.M03.ConnectionFamily
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Connection.Koszul
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Connection.Regularity
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom























set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology
open Bundle Manifold Set

universe u

namespace PoincareConjecture.RicciFlow.Local

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem contMDiffWithinAt_clm_apply_iff
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ F]
    {f : ℝ × M → F →L[ℝ] G} {S : Set (ℝ × M)} {p : ℝ × M} :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, F →L[ℝ] G) ∞ f S p ↔
      ∀ v : F, ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, G) ∞
        (fun q ↦ f q v) S p := by
  constructor
  · intro h v
    exact h.clm_apply contMDiffWithinAt_const
  · intro h
    let d := Module.finrank ℝ F
    have hd : d = Module.finrank ℝ (Fin d → ℝ) :=
      (Module.finrank_fin_fun ℝ).symm
    let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
    let e₂ := (e₁.arrowCongr (ContinuousLinearEquiv.refl ℝ G)).trans
      (ContinuousLinearEquiv.piRing (Fin d))
    have hc : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
        𝓘(ℝ, Fin d → G) ∞ (fun q ↦ e₂ (f q)) S p := by
      apply contMDiffWithinAt_pi_space.mpr
      intro i
      change ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, G) ∞
        (fun q ↦ f q (e₁.symm (Pi.single i 1))) S p
      exact h (e₁.symm (Pi.single i 1))
    have hb := (contMDiffWithinAt_const
      (c := e₂.symm.toContinuousLinearMap)).clm_apply hc
    simpa only [ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using hb

theorem contMDiffOn_family_metric_pair
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    {U : Set M} (X Y : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% Y) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (g p.1).inner p.2 (X p.2) (Y p.2)) (J ×ˢ U) := by
  have hX' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2
        (X p.2)) (J ×ˢ U) :=
    hX.comp contMDiffOn_snd (fun _ hp => hp.2)
  have hY' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2
        (Y p.2)) (J ×ˢ U) :=
    hY.comp contMDiffOn_snd (fun _ hp => hp.2)
  have hg' := hg.mono (Set.prod_mono subset_rfl (subset_univ U))
  have hfirst : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M =>
        (⟨p.2, ((g p.1).inner p.2) (X p.2)⟩ :
          TotalSpace (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
            (fun x => TangentSpace (𝓡 n) x →L[ℝ] ℝ))) (J ×ˢ U) := by
    exact ContMDiffOn.clm_bundle_apply
      (F₁ := EuclideanSpace ℝ (Fin n))
      (F₂ := EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (E₁ := fun x : M => TangentSpace (𝓡 n) x)
      (E₂ := fun x : M => TangentSpace (𝓡 n) x →L[ℝ] ℝ)
      (ϕ := fun p : ℝ × M => (g p.1).inner p.2)
      (b := fun p : ℝ × M => p.2) hg' hX'
  have hpair := ContMDiffOn.clm_bundle_apply
    (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := ℝ)
    (E₁ := fun x : M => TangentSpace (𝓡 n) x)
    (E₂ := fun _ : M => ℝ)
    (ϕ := fun p : ℝ × M => ((g p.1).inner p.2) (X p.2))
    (b := fun p : ℝ × M => p.2) hfirst hY'
  intro p hp
  exact (Bundle.contMDiffWithinAt_totalSpace.mp (hpair p hp)).2

theorem contMDiffOn_family_spatial_mvfderiv
    {f : ℝ → M → ℝ} {J : Set ℝ} {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry f) (J ×ˢ U))
    (X : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ mvfderiv (𝓡 n) (f p.1) p.2 (X p.2)) (J ×ˢ U) := by
  intro p hp
  have hf' : ContMDiffWithinAt
      (((𝓘(ℝ, ℝ)).prod (𝓡 n)).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun q : (ℝ × M) × M => f q.1.1 q.2) ((J ×ˢ U) ×ˢ U) (p, p.2) :=
    (hf (p.1, p.2) hp).comp (p, p.2)
      (contMDiffWithinAt_fst.fst.prodMk contMDiffWithinAt_snd)
      (fun (_q : (ℝ × M) × M) (hq : _q ∈ (J ×ˢ U) ×ˢ U) =>
        ⟨hq.1.1, hq.2⟩)
  have hderiv := ContMDiffWithinAt.mfderivWithin
    (n := ∞) (m := ∞) (f := fun q : ℝ × M => f q.1) (g := Prod.snd) hf'
    contMDiffWithinAt_snd hp (fun q hq => hq.2) (by norm_num) hU.uniqueMDiffOn
  have hX' : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun q : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q.2
        (X q.2)) (J ×ˢ U) p :=
    (hX p.2 hp.2).comp p contMDiffWithinAt_snd (fun _ hq => hq.2)
  have happ := ContMDiffWithinAt.clm_apply_of_inCoordinates
    (b₁ := Prod.snd) (b₂ := fun q : ℝ × M => f q.1 q.2)
    hderiv hX' (hf p hp)
  have hscalar : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => mfderivWithin (𝓡 n) 𝓘(ℝ, ℝ)
        (f q.1) U q.2 (X q.2)) (J ×ˢ U) p := by
    have hs := (Bundle.contMDiffWithinAt_totalSpace.mp happ).2
    simpa only [trivializationAt_model_space_apply] using hs
  apply hscalar.congr_of_eventuallyEq_of_mem _ hp
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [mfderivWithin_of_mem_nhds (hU.mem_nhds hq.2)]
  rfl

theorem contMDiffOn_family_koszulExpression
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    {U : Set M} (hU : IsOpen U)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦
        mvfderiv (𝓡 n) (fun y ↦ (g p.1).inner y (Y y) (Z y)) p.2 (X p.2) +
        mvfderiv (𝓡 n) (fun y ↦ (g p.1).inner y (Z y) (X y)) p.2 (Y p.2) -
        mvfderiv (𝓡 n) (fun y ↦ (g p.1).inner y (X y) (Y y)) p.2 (Z p.2) +
        (g p.1).inner p.2 (VectorField.mlieBracket (𝓡 n) X Y p.2) (Z p.2) -
        (g p.1).inner p.2 (Y p.2) (VectorField.mlieBracket (𝓡 n) X Z p.2) -
        (g p.1).inner p.2 (X p.2) (VectorField.mlieBracket (𝓡 n) Y Z p.2)) (J ×ˢ U) := by
  letI : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞) (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  letI : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  have hYZ := contMDiffOn_family_metric_pair hg Y Z hY hZ
  have hZX := contMDiffOn_family_metric_pair hg Z X hZ hX
  have hXY := contMDiffOn_family_metric_pair hg X Y hX hY
  have hXdir := contMDiffOn_family_spatial_mvfderiv (f := fun t x =>
      (g t).inner x (Y x) (Z x)) (J := J) (U := U) hU hYZ X hX
  have hYdir := contMDiffOn_family_spatial_mvfderiv (f := fun t x =>
      (g t).inner x (Z x) (X x)) (J := J) (U := U) hU hZX Y hY
  have hZdir := contMDiffOn_family_spatial_mvfderiv (f := fun t x =>
      (g t).inner x (X x) (Y x)) (J := J) (U := U) hU hXY Z hZ
  have hbrXYWithin := hX.mlieBracketWithin_vectorField (m := ⊤) (n := ⊤)
    hY hU.uniqueMDiffOn (by simp)
  have hbrXZWithin := hX.mlieBracketWithin_vectorField (m := ⊤) (n := ⊤)
    hZ hU.uniqueMDiffOn (by simp)
  have hbrYZWithin := hY.mlieBracketWithin_vectorField (m := ⊤) (n := ⊤)
    hZ hU.uniqueMDiffOn (by simp)
  have hbrXY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (VectorField.mlieBracket (𝓡 n) X Y)) U := by
    intro x hx
    apply (hbrXYWithin x hx).congr_of_eventuallyEq_of_mem _ hx
    filter_upwards [self_mem_nhdsWithin] with q hq
    change (⟨q, VectorField.mlieBracket (𝓡 n) X Y q⟩ : TangentBundle (𝓡 n) M) =
      (⟨q, VectorField.mlieBracketWithin (𝓡 n) X Y U q⟩ : TangentBundle (𝓡 n) M)
    rw [VectorField.mlieBracketWithin_of_isOpen hU hq]
  have hbrXZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (VectorField.mlieBracket (𝓡 n) X Z)) U := by
    intro x hx
    apply (hbrXZWithin x hx).congr_of_eventuallyEq_of_mem _ hx
    filter_upwards [self_mem_nhdsWithin] with q hq
    change (⟨q, VectorField.mlieBracket (𝓡 n) X Z q⟩ : TangentBundle (𝓡 n) M) =
      (⟨q, VectorField.mlieBracketWithin (𝓡 n) X Z U q⟩ : TangentBundle (𝓡 n) M)
    rw [VectorField.mlieBracketWithin_of_isOpen hU hq]
  have hbrYZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (VectorField.mlieBracket (𝓡 n) Y Z)) U := by
    intro x hx
    apply (hbrYZWithin x hx).congr_of_eventuallyEq_of_mem _ hx
    filter_upwards [self_mem_nhdsWithin] with q hq
    change (⟨q, VectorField.mlieBracket (𝓡 n) Y Z q⟩ : TangentBundle (𝓡 n) M) =
      (⟨q, VectorField.mlieBracketWithin (𝓡 n) Y Z U q⟩ : TangentBundle (𝓡 n) M)
    rw [VectorField.mlieBracketWithin_of_isOpen hU hq]
  have hpairbrXY := contMDiffOn_family_metric_pair hg
    (VectorField.mlieBracket (𝓡 n) X Y) Z hbrXY hZ
  have hpairbrXZ := contMDiffOn_family_metric_pair hg
    Y (VectorField.mlieBracket (𝓡 n) X Z) hY hbrXZ
  have hpairbrYZ := contMDiffOn_family_metric_pair hg
    X (VectorField.mlieBracket (𝓡 n) Y Z) hX hbrYZ
  have hsum := (((((hXdir.add hYdir).sub hZdir).add hpairbrXY).sub
    hpairbrXZ).sub hpairbrYZ)
  convert hsum using 1
  funext p
  rfl

theorem contMDiffOn_connection_family
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (D : (t : ℝ) → LeviCivitaData (g t))
    {U : Set M} (hU : IsOpen U)
    (Y : (x : M) → TangentSpace (𝓡 n) x)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) p.2
        (E := fun x : M =>
          TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x)
        ((D p.1).connection Y p.2)) (J ×ˢ U) := by
  intro p hp
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) p.2
  have hep : p.2 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p.2
  let frame (v : EuclideanSpace ℝ (Fin n)) (q : M) : TangentSpace (𝓡 n) q :=
    e.symmL ℝ q v
  have hframe (v : EuclideanSpace ℝ (Fin n)) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (frame v)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff (IB := (𝓡 n)) (n := ∞)]
    refine (contMDiffOn_const (c := v)).congr ?_
    intro q hq
    simpa [frame, Trivialization.symmL_apply _ hq] using
      congrArg Prod.snd (e.apply_mk_symm hq v)
  let G (q : ℝ × M) :
      EuclideanSpace ℝ (Fin n) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (fun x => TangentSpace (𝓡 n) x →L[ℝ] ℝ) p.2 q.2 p.2 q.2
      ((g q.1).inner q.2)
  let B (q : ℝ × M) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n)) p.2 q.2 p.2 q.2
      ((D q.1).connection Y q.2)
  have hG : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      G (J ×ˢ U) p := by
    have hg' := hg.mono (Set.prod_mono subset_rfl (subset_univ U))
    let H : ℝ × M →
        TotalSpace (EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
          (fun x => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ) :=
      fun q => TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) q.2
        (E := fun x : M =>
          TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
        ((g q.1).inner q.2)
    have hmetric := (contMDiffWithinAt_hom_bundle H
      (s := J ×ˢ U) (x₀ := p)).mp (hg' p hp)
    simpa [G, H] using hmetric.2
  have hGinv (q : ℝ × M) (hq : q.2 ∈ e.baseSet) : (G q).IsInvertible := by
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(g q.1).toRiemannianMetric⟩
    rw [show G q =
        (e.continuousLinearEquivAt ℝ q.2 hq).arrowCongr
          (1 : ℝ ≃L[ℝ] ℝ) ∘L ((g q.1).inner q.2) ∘L
          (e.continuousLinearEquivAt ℝ q.2 hq).symm by
      ext a b
      dsimp [G]
      rw [inCoordinates_apply_eq₂
        (F₁ := EuclideanSpace ℝ (Fin n))
        (F₂ := EuclideanSpace ℝ (Fin n)) (F₃ := ℝ)
        (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
        (E₃ := fun _ : M => ℝ) hq hq (by simp)]
      simp [e]
      rfl]
    letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) q.2) :=
      VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) q.2
    have hinj : Function.Injective ((g q.1).inner q.2).toLinearMap := by
      intro a b hab
      apply ext_inner_right ℝ
      intro c
      exact congrArg (fun L : TangentSpace (𝓡 n) q.2 →L[ℝ] ℝ => L c) hab
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) q.2) =
        Module.finrank ℝ (TangentSpace (𝓡 n) q.2 →L[ℝ] ℝ) := by
      calc
        _ = Module.finrank ℝ (Module.Dual ℝ (TangentSpace (𝓡 n) q.2)) :=
          Subspace.dual_finrank_eq.symm
        _ = _ := (LinearMap.toContinuousLinearMap :
          (TangentSpace (𝓡 n) q.2 →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
            (TangentSpace (𝓡 n) q.2 →L[ℝ] ℝ)).finrank_eq
    let j : TangentSpace (𝓡 n) q.2 ≃L[ℝ]
        (TangentSpace (𝓡 n) q.2 →L[ℝ] ℝ) :=
      ((g q.1).inner q.2).toLinearMap.linearEquivOfInjective hinj hdim
        |>.toContinuousLinearEquiv
    have hi : ((g q.1).inner q.2).IsInvertible := by
      rw [show (g q.1).inner q.2 = j by
        ext a b
        rfl]
      exact ContinuousLinearMap.isInvertible_equiv
    have hdual : ((e.continuousLinearEquivAt ℝ q.2 hq).arrowCongr
        (1 : ℝ ≃L[ℝ] ℝ) :
        (TangentSpace (𝓡 n) q.2 →L[ℝ] ℝ) →L[ℝ]
          (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).IsInvertible :=
      ContinuousLinearMap.isInvertible_equiv
    have hT : ((e.continuousLinearEquivAt ℝ q.2 hq).symm :
        EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) q.2).IsInvertible :=
      ContinuousLinearMap.isInvertible_equiv
    exact hdual.comp (hi.comp hT)
  have hGinv_smooth : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      𝓘(ℝ, (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) ∞
      (fun q => ContinuousLinearMap.inverse (G q)) (J ×ˢ U) p :=
    ContMDiffAt.comp_contMDiffWithinAt p
      ((hGinv p hep).contDiffAt_map_inverse.contMDiffAt) hG
  have hbase_event : ∀ᶠ q in 𝓝[J ×ˢ U] p, q.2 ∈ e.baseSet :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (continuous_snd.continuousAt.preimage_mem_nhds
        (e.open_baseSet.mem_nhds hep))
  have hsmall_mem : J ×ˢ (U ∩ e.baseSet) ∈ 𝓝[J ×ˢ U] p := by
    filter_upwards [self_mem_nhdsWithin, hbase_event] with q hq hqe
    exact ⟨hq.1, hq.2, hqe⟩
  have hB : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      B (J ×ˢ U) p := by
    apply contMDiffWithinAt_clm_apply_iff.mpr
    intro v
    have hQv : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓡 n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∞
        (fun q => (G q).comp (B q) v) (J ×ˢ U) p := by
      apply contMDiffWithinAt_clm_apply_iff.mpr
      intro w
      have hR := contMDiffOn_family_koszulExpression hg
        (hU.inter e.open_baseSet) (frame v) Y (frame w)
        ((hframe v).mono inter_subset_right)
        (hY.mono inter_subset_left)
        ((hframe w).mono inter_subset_right)
      have hRbig := (hR p ⟨hp.1, ⟨hp.2, hep⟩⟩).mono_of_mem_nhdsWithin hsmall_mem
      have heq : ∀ᶠ q in 𝓝[J ×ˢ U] p,
          (G q) (B q v) w = (1 / 2 : ℝ) *
            (mvfderiv (𝓡 n) (fun y => (g q.1).inner y (Y y) (frame w y)) q.2
                (frame v q.2) +
             mvfderiv (𝓡 n) (fun y => (g q.1).inner y (frame w y) (frame v y)) q.2
                (Y q.2) -
             mvfderiv (𝓡 n) (fun y => (g q.1).inner y (frame v y) (Y y)) q.2
                (frame w q.2) +
             (g q.1).inner q.2 (VectorField.mlieBracket (𝓡 n) (frame v) Y q.2)
                (frame w q.2) -
             (g q.1).inner q.2 (Y q.2)
                (VectorField.mlieBracket (𝓡 n) (frame v) (frame w) q.2) -
             (g q.1).inner q.2 (frame v q.2)
                (VectorField.mlieBracket (𝓡 n) Y (frame w) q.2)) := by
        filter_upwards [self_mem_nhdsWithin, hbase_event] with q hq hqe
        have hXq := ((hframe v q.2 hqe).contMDiffAt
          (e.open_baseSet.mem_nhds hqe)).mdifferentiableAt (by simp)
        have hYq := ((hY q.2 hq.2).contMDiffAt
          (hU.mem_nhds hq.2)).mdifferentiableAt (by simp)
        have hZq := ((hframe w q.2 hqe).contMDiffAt
          (e.open_baseSet.mem_nhds hqe)).mdifferentiableAt (by simp)
        rw [show (G q) (B q v) w =
            (g q.1).inner q.2 ((D q.1).connection Y q.2 (frame v q.2))
              (frame w q.2) by
          dsimp [G, B]
          rw [inCoordinates_apply_eq₂
            (F₁ := EuclideanSpace ℝ (Fin n))
            (F₂ := EuclideanSpace ℝ (Fin n)) (F₃ := ℝ)
            (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
            (E₃ := fun _ : M => ℝ) hqe hqe (by simp)]
          rw [ContinuousLinearMap.inCoordinates_eq hqe hqe]
          simp only [Trivial.fiberBundle_trivializationAt',
            Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
            ContinuousLinearMap.comp_apply]
          have hcancel (z : TangentSpace (𝓡 n) q.2) :
              e.symmL ℝ q.2 ((e.continuousLinearEquivAt ℝ q.2 hqe) z) = z := by
            rw [← e.symm_continuousLinearEquivAt_eq' hqe]
            exact (e.continuousLinearEquivAt ℝ q.2 hqe).symm_apply_apply z
          rw [← Trivialization.symmL_apply (R := ℝ) e hqe]
          rw [Trivialization.symm_continuousLinearEquivAt_eq' (R := ℝ) e hqe]
          change (g q.1).inner q.2
            (e.symmL ℝ q.2 ((e.continuousLinearEquivAt ℝ q.2 hqe)
              ((D q.1).connection Y q.2 (e.symmL ℝ q.2 v))))
            (e.symm q.2 w) = _
          rw [hcancel]
          rw [← Trivialization.symmL_apply (R := ℝ) e hqe w]]
        linarith only [(D q.1).koszul _ _ _ hXq hYq hZq]
      have hhalf : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod (𝓡 n))
          𝓘(ℝ, ℝ) ∞ (fun _ => (1 / 2 : ℝ)) (J ×ˢ U) p :=
        contMDiffWithinAt_const
      have hscalar := (hhalf.smul hRbig).congr_of_eventuallyEq_of_mem heq hp
      simpa only [ContinuousLinearMap.comp_apply] using hscalar
    have hBv := hGinv_smooth.clm_apply hQv
    have heq : ∀ᶠ q in 𝓝[J ×ˢ U] p,
        (ContinuousLinearMap.inverse (G q)) ((G q).comp (B q) v) = B q v := by
      filter_upwards [hbase_event] with q hq
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
        congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ]
            EuclideanSpace ℝ (Fin n) => L (B q v))
          (ContinuousLinearMap.IsInvertible.inverse_comp_self (hGinv q hq))
    exact hBv.congr_of_eventuallyEq_of_mem (Filter.EventuallyEq.symm heq) hp
  let F : ℝ × M →
      TotalSpace (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (fun x => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x) :=
    fun q => TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) q.2
      (E := fun x : M =>
        TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x)
      ((D q.1).connection Y q.2)
  have htotal := (contMDiffWithinAt_hom_bundle F
    (s := J ×ˢ U) (x₀ := p)).mpr ⟨contMDiffWithinAt_snd, hB⟩
  exact htotal




theorem contMDiffOn_connection_family_apply
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (D : (t : ℝ) → LeviCivitaData (g t))
    {U : Set M} (hU : IsOpen U)
    (Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) p.2
        (E := fun x : M => TangentSpace (𝓡 n) x)
        ((D p.1).connection Y p.2 (Z p.2))) (J ×ˢ U) := by
  have hZ' : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) p.2
        (E := fun x : M => TangentSpace (𝓡 n) x) (Z p.2)) (J ×ˢ U) :=
    hZ.comp contMDiffOn_snd (fun _ hp => hp.2)
  exact ContMDiffOn.clm_bundle_apply
    (contMDiffOn_connection_family hg D hU Y hY) hZ'

end PoincareConjecture.RicciFlow.Local
