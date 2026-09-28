import PoincareConjecture.Proofs.M01.ConnectionExistenceKoszul
import PoincareConjecture.Proofs.M01.ConnectionRiesz
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle Manifold Set

universe u

namespace PoincareConjecture.ConnectionExistence

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

private theorem contMDiffAt_clm_apply_iff
    [IsManifold (𝓡 n) ∞ M]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ F]
    {f : M → F →L[ℝ] G} {p : M} :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, F →L[ℝ] G) ∞ f p ↔
      ∀ v : F, ContMDiffAt (𝓡 n) 𝓘(ℝ, G) ∞ (fun q => f q v) p := by
  constructor
  · intro h v
    exact h.clm_apply (contMDiffAt_const (c := v))
  · intro h
    rw [contMDiffAt_iff_source]
    rw [contMDiffWithinAt_iff_contDiffWithinAt]
    apply contDiffWithinAt_infty.mpr
    intro m
    let d := Module.finrank ℝ F
    have hd : d = Module.finrank ℝ (Fin d → ℝ) :=
      (Module.finrank_fin_fun ℝ).symm
    let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
    let e₂ := (e₁.arrowCongr (ContinuousLinearEquiv.refl ℝ G)).trans
      (ContinuousLinearEquiv.piRing (Fin d))
    let c : (EuclideanSpace ℝ (Fin n)) → F →L[ℝ] G := fun z => f ((extChartAt (𝓡 n) p).symm z)
    have hs : ∀ i : Fin d, ContDiffWithinAt ℝ m
        (fun z => (e₂ (c z)) i) (Set.range (𝓡 n)) (extChartAt (𝓡 n) p p) := by
      intro i
      have hi := (contMDiffAt_iff_source.mp (h (e₁.symm (Pi.single i 1)))).contDiffWithinAt
      have hi' : ContDiffWithinAt ℝ m
          (fun z => f ((extChartAt (𝓡 n) p).symm z) (e₁.symm (Pi.single i 1)))
          (Set.range (𝓡 n)) (extChartAt (𝓡 n) p p) := by
        exact hi.of_le (mod_cast le_top)
      have heq : (fun z => e₂ (c z) i) =
          (fun z => f ((extChartAt (𝓡 n) p).symm z)
            (e₁.symm (Pi.single i 1))) := by
        funext z
        simp [c, e₂, ContinuousLinearEquiv.trans_apply,
          ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.refl_apply,
          ContinuousLinearEquiv.piRing, LinearEquiv.piRing_apply]
      rw [heq]
      exact hi'
    have hc : ContDiffWithinAt ℝ m (fun z => e₂ (c z))
        (Set.range (𝓡 n)) (extChartAt (𝓡 n) p p) := by
      rw [contDiffWithinAt_pi]
      exact hs
    have hback : ContDiffWithinAt ℝ m (fun z => e₂.symm (e₂ (c z)))
        (Set.range (𝓡 n)) (extChartAt (𝓡 n) p p) :=
      (contDiffWithinAt_const (c := e₂.symm.toContinuousLinearMap)).clm_apply hc
    simpa [c, Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hback

variable [IsManifold (𝓡 n) ∞ M]

private noncomputable def chartFrame (p : M) (v : (EuclideanSpace ℝ (Fin n))) (q : M) :
    TangentSpace (𝓡 n) q :=
  (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).symmL ℝ q v

private theorem chartFrame_contMDiffOn (p : M) (v : (EuclideanSpace ℝ (Fin n))) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞ (fun q =>
      TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) q (chartFrame p v q))
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet := by
  rw [(trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
    p).contMDiffOn_section_baseSet_iff (IB := (𝓡 n)) (n := ∞)]
  refine (contMDiffOn_const (c := v)).congr ?_
  intro q hq
  simpa [chartFrame, Bundle.Trivialization.symmL_apply _ hq] using
    congrArg Prod.snd
      ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).apply_mk_symm hq v)

private theorem chartFrame_apply_inCoordinates (p q : M) (v : (EuclideanSpace ℝ (Fin n)))
    (hq : q ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).baseSet) :
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
      ⟨q, chartFrame p v q⟩).2 = v := by
  simpa [chartFrame, Bundle.Trivialization.symmL_apply _ hq] using
    congrArg Prod.snd
      ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).apply_mk_symm hq v)

private theorem koszulRHS_contMDiffOn
    (g : RiemannianMetric n M)
    {U : Set M} (hU : IsOpen U)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞ (T% Z) U) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ) ∞ (koszulRHS g X Y Z) U := by
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
  have hXY : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun q => g.inner q (X q) (Y q)) U := hX.inner_bundle hY
  have hZX : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun q => g.inner q (Z q) (X q)) U := hZ.inner_bundle hX
  have hYZ : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun q => g.inner q (Y q) (Z q)) U := hY.inner_bundle hZ
  have hXY_at := (hXY x hx).contMDiffAt (hU.mem_nhds hx)
  have hZX_at := (hZX x hx).contMDiffAt (hU.mem_nhds hx)
  have hYZ_at := (hYZ x hx).contMDiffAt (hU.mem_nhds hx)
  have hXdir := ContMDiffAt.clm_apply_of_inCoordinates
    (b₁ := id) (b₂ := fun q => (g.inner q) (Y q) (Z q))
    (hYZ_at.mfderiv_const (m := ∞) (n := ∞) (by simp)) hXp hYZ_at
  have hYdir := ContMDiffAt.clm_apply_of_inCoordinates
    (b₁ := id) (b₂ := fun q => (g.inner q) (Z q) (X q))
    (hZX_at.mfderiv_const (m := ∞) (n := ∞) (by simp)) hYp hZX_at
  have hZdir := ContMDiffAt.clm_apply_of_inCoordinates
    (b₁ := id) (b₂ := fun q => (g.inner q) (X q) (Y q))
    (hXY_at.mfderiv_const (m := ∞) (n := ∞) (by simp)) hZp hXY_at
  have hbrXY := hXp.mlieBracket_vectorField (m := ⊤) (n := ⊤) hYp (by simp)
  have hbrXZ := hXp.mlieBracket_vectorField (m := ⊤) (n := ⊤) hZp (by simp)
  have hbrYZ := hYp.mlieBracket_vectorField (m := ⊤) (n := ⊤) hZp (by simp)
  have hpairbrXY := hbrXY.inner_bundle hZp
  have hpairbrXZ := hYp.inner_bundle hbrXZ
  have hpairbrYZ := hXp.inner_bundle hbrYZ
  have hXdir' := (Bundle.contMDiffAt_totalSpace.mp hXdir).2
  have hYdir' := (Bundle.contMDiffAt_totalSpace.mp hYdir).2
  have hZdir' := (Bundle.contMDiffAt_totalSpace.mp hZdir).2
  have hsum := (((((hXdir'.add hYdir').sub hZdir').add hpairbrXY).sub
    hpairbrXZ).sub hpairbrYZ)
  convert (hsum.contMDiffWithinAt.mono (subset_univ U)) using 1
  funext y
  simp only [id_eq, trivializationAt_model_space_apply, Pi.add_apply]
  change
    (NormedSpace.fromTangentSpace _
          (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun q => ((g.inner q) (Y q)) (Z q)) y (X y)) +
        NormedSpace.fromTangentSpace _
          (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun q => ((g.inner q) (Z q)) (X q)) y (Y y)) -
      NormedSpace.fromTangentSpace _
        (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun q => ((g.inner q) (X q)) (Y q)) y (Z y))) +
      inner ℝ (VectorField.mlieBracket (𝓡 n) X Y y) (Z y) -
        inner ℝ (Y y) (VectorField.mlieBracket (𝓡 n) X Z y) -
      inner ℝ (X y) (VectorField.mlieBracket (𝓡 n) Y Z y) =
    (NormedSpace.fromTangentSpace _
          (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun q => ((g.inner q) (Y q)) (Z q)) y (X y)) +
        NormedSpace.fromTangentSpace _
          (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun q => ((g.inner q) (Z q)) (X q)) y (Y y)) -
      NormedSpace.fromTangentSpace _
        (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun q => ((g.inner q) (X q)) (Y q)) y (Z y))) +
      inner ℝ (VectorField.mlieBracket (𝓡 n) X Y y) (Z y) -
        inner ℝ (Y y) (VectorField.mlieBracket (𝓡 n) X Z y) -
      inner ℝ (X y) (VectorField.mlieBracket (𝓡 n) Y Z y)
  ring

theorem koszul_operator_contMDiffOn
    (g : RiemannianMetric n M)
    (A : (Y : (x : M) → TangentSpace (𝓡 n) x) →
      (x : M) → TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x)
    (hA : ∀ (X Y Z : (x : M) → TangentSpace (𝓡 n) x) {x : M},
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) (T% X) x →
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) (T% Y) x →
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) (T% Z) x →
      g.inner x (A Y x (X x)) (Z x) =
        (1 / 2 : ℝ) * koszulRHS g X Y Z x)
    {U : Set M} (hU : IsOpen U)
    (Y : (x : M) → TangentSpace (𝓡 n) x)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞ (T% Y) U) :
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)))) ∞
      (fun x => TotalSpace.mk' ((EuclideanSpace ℝ (Fin n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n))) x (A Y x)) U := by
  intro p hp
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p
  have hep : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  have heopen : IsOpen e.baseSet := e.open_baseSet
  let G : (q : M) → (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ := fun q =>
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
      ((EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) (fun x => TangentSpace (𝓡 n) x →L[ℝ] ℝ)
      p q p q (g.inner q)
  let B : (q : M) → (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) := fun q =>
    ContinuousLinearMap.inCoordinates (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
      (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p q p q (A Y q)
  have hG : ContMDiffAt (𝓡 n)
      𝓘(ℝ, (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) ∞ G p := by
    dsimp [G]
    have hg := g.contMDiff p
    have hc := (contMDiffAt_hom_bundle (fun q =>
      (TotalSpace.mk' ((EuclideanSpace ℝ (Fin n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) q (g.inner q) :
        TotalSpace ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
          (fun x => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)))).mp hg
    exact hc.2
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : M → Type _) p
  let : CompleteSpace (TangentSpace (𝓡 n) p) := FiniteDimensional.complete ℝ _
  have hGinv : (G p).IsInvertible := by
    let eT := e.continuousLinearEquivAt ℝ p hep
    let eDual := eT.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
    rw [show G p =
      (eDual : (TangentSpace (𝓡 n) p →L[ℝ] ℝ) →L[ℝ] ((EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)) ∘L
        (g.inner p) ∘L (eT.symm : (EuclideanSpace ℝ (Fin n)) →L[ℝ] TangentSpace (𝓡 n) p) by
      ext v w
      dsimp [G]
      rw [inCoordinates_apply_eq₂ (F₁ := EuclideanSpace ℝ (Fin n))
        (F₂ := EuclideanSpace ℝ (Fin n)) (F₃ := ℝ)
        (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
        (E₃ := fun _ : M => ℝ) hep hep (by simp)]
      simp [e, eT, eDual, ContinuousLinearEquiv.arrowCongr_apply,
        ContinuousLinearEquiv.refl_apply]
    ]
    have hi : (g.inner p).IsInvertible := metricInner_isInvertible g p
    have hdual : (eDual : (TangentSpace (𝓡 n) p →L[ℝ] ℝ) →L[ℝ]
        ((EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)).IsInvertible := ContinuousLinearMap.isInvertible_equiv
    have hT : (eT.symm : (EuclideanSpace ℝ (Fin n)) →L[ℝ] TangentSpace (𝓡 n) p).IsInvertible :=
      ContinuousLinearMap.isInvertible_equiv
    exact hdual.comp (hi.comp hT)
  have hGinv_smooth : ContMDiffAt (𝓡 n)
      𝓘(ℝ, ((EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin n))) ∞
      (fun q => ContinuousLinearMap.inverse (G q)) p := by
    exact (hGinv.contDiffAt_map_inverse.contMDiffAt.comp p hG)
  have hB : ContMDiffAt (𝓡 n)
      𝓘(ℝ, (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n))) ∞ B p := by
    apply (contMDiffAt_clm_apply_iff).2
    intro v
    have hQv : ContMDiffAt (𝓡 n) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ) ∞
        (fun q => (G q).comp (B q) v) p := by
      apply (contMDiffAt_clm_apply_iff).2
      intro w
      have hv : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞
          (T% (chartFrame p v)) p := by
        exact (chartFrame_contMDiffOn p v p hep).contMDiffAt
          (e.open_baseSet.mem_nhds hep)
      have hw : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞
          (T% (chartFrame p w)) p := by
        exact (chartFrame_contMDiffOn p w p hep).contMDiffAt
          (e.open_baseSet.mem_nhds hep)
      have hvU : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞
          (T% (chartFrame p v)) (U ∩ e.baseSet) :=
        (chartFrame_contMDiffOn p v).mono inter_subset_right
      have hwU : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞
          (T% (chartFrame p w)) (U ∩ e.baseSet) :=
        (chartFrame_contMDiffOn p w).mono inter_subset_right
      have hYU : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n)))) ∞
          (T% Y) (U ∩ e.baseSet) :=
        hY.mono inter_subset_left
      have hR := koszulRHS_contMDiffOn g (hU.inter e.open_baseSet)
        (chartFrame p v) Y (chartFrame p w) hvU hYU hwU
      have heq : ∀ᶠ q in 𝓝 p, (G q) (B q v) w =
          (1 / 2 : ℝ) * koszulRHS g (chartFrame p v) Y (chartFrame p w) q := by
        filter_upwards [hU.mem_nhds hp, e.open_baseSet.mem_nhds hep] with q hq hqe
        have hXq : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
            (T% (chartFrame p v)) q :=
          ((chartFrame_contMDiffOn p v q hqe).contMDiffAt
            (e.open_baseSet.mem_nhds hqe)).mdifferentiableAt (by simp)
        have hYq := (hY q hq).contMDiffAt (hU.mem_nhds hq) |>.mdifferentiableAt (by simp)
        have hZq : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))))
            (T% (chartFrame p w)) q :=
          ((chartFrame_contMDiffOn p w q hqe).contMDiffAt
            (e.open_baseSet.mem_nhds hqe)).mdifferentiableAt (by simp)
        rw [show (G q) (B q v) w =
          g.inner q (A Y q (chartFrame p v q)) (chartFrame p w q) by
          dsimp [G, B]
          rw [inCoordinates_apply_eq₂ (F₁ := EuclideanSpace ℝ (Fin n))
            (F₂ := EuclideanSpace ℝ (Fin n)) (F₃ := ℝ)
            (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
            (E₃ := fun _ : M => ℝ) hqe hqe (by simp)]
          rw [ContinuousLinearMap.inCoordinates_eq hqe hqe]
          simp only [Trivial.fiberBundle_trivializationAt',
            Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
            ContinuousLinearMap.comp_apply]
          have hcancel : ∀ z : TangentSpace (𝓡 n) q,
              e.symmL ℝ q ((e.continuousLinearEquivAt ℝ q hqe) z) = z := by
            intro z
            rw [← e.symm_continuousLinearEquivAt_eq' hqe]
            exact (e.continuousLinearEquivAt ℝ q hqe).symm_apply_apply z
          have hcancel' : ∀ z : TangentSpace (𝓡 n) q,
              (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p).symmL ℝ q
                  ((trivializationAt (EuclideanSpace ℝ (Fin n))
                    (TangentSpace (𝓡 n)) p).continuousLinearEquivAt ℝ q hqe z) = z := by
            simpa [e] using hcancel
          rw [← Bundle.Trivialization.symmL_apply (R := ℝ) e hqe]
          rw [Bundle.Trivialization.symm_continuousLinearEquivAt_eq' (R := ℝ) e hqe]
          dsimp [e]
          rw [hcancel']
          simp only [chartFrame]
          rw [Bundle.Trivialization.symmL_apply (R := ℝ)
            (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) p) hqe w]
        ]
        exact hA _ _ _ hXq hYq hZq
      have hhalf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M => (1 / 2 : ℝ)) p :=
        contMDiffAt_const
      have hscalar : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun q => (G q) (B q v) w) p :=
        (hhalf.smul
          ((hR p ⟨hp, hep⟩).contMDiffAt
            ((hU.inter e.open_baseSet).mem_nhds ⟨hp, hep⟩))).congr_of_eventuallyEq
          heq
      convert hscalar using 1
      simp only [ContinuousLinearMap.comp_apply]
    have hBv' := hGinv_smooth.clm_apply hQv
    have heqB : ∀ᶠ q in 𝓝 p,
        (ContinuousLinearMap.inverse (G q)) ((G q).comp (B q) v) = B q v := by
      filter_upwards [hU.mem_nhds hp, e.open_baseSet.mem_nhds hep] with q hq hqe
      have hGq : (G q).IsInvertible := by
        rw [show G q =
          (e.continuousLinearEquivAt ℝ q hqe).arrowCongr (1 : ℝ ≃L[ℝ] ℝ) ∘L
            (g.inner q) ∘L
            (e.continuousLinearEquivAt ℝ q hqe).symm by
          ext a b
          dsimp [G]
          rw [inCoordinates_apply_eq₂ (F₁ := EuclideanSpace ℝ (Fin n))
            (F₂ := EuclideanSpace ℝ (Fin n)) (F₃ := ℝ)
            (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
            (E₃ := fun _ : M => ℝ) hqe hqe (by simp)]
          simp [e]
          rfl
        ]
        have hi : (g.inner q).IsInvertible := metricInner_isInvertible g q
        have hdual :
            ((e.continuousLinearEquivAt ℝ q hqe).arrowCongr
              (1 : ℝ ≃L[ℝ] ℝ) :
              (TangentSpace (𝓡 n) q →L[ℝ] ℝ) →L[ℝ]
                ((EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)).IsInvertible :=
          ContinuousLinearMap.isInvertible_equiv
        have hT :
            ((e.continuousLinearEquivAt ℝ q hqe).symm :
              (EuclideanSpace ℝ (Fin n)) →L[ℝ] TangentSpace (𝓡 n) q).IsInvertible :=
          ContinuousLinearMap.isInvertible_equiv
        exact hdual.comp (hi.comp hT)
      have hcomp := ContinuousLinearMap.IsInvertible.inverse_comp_self hGq
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
        congrArg (fun L : (EuclideanSpace ℝ (Fin n)) →L[ℝ]
          (EuclideanSpace ℝ (Fin n)) => L ((B q) v)) hcomp
    change ContMDiffAt (𝓡 n) 𝓘(ℝ, (EuclideanSpace ℝ (Fin n))) ∞ (fun q => (B q) v) p
    exact hBv'.congr_of_eventuallyEq (Filter.EventuallyEq.symm heqB)
  have htotal := (contMDiffAt_hom_bundle (fun q =>
      (TotalSpace.mk' ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n))) q (A Y q) :
        TotalSpace ((EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)))
          (fun x => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x)))).mpr
      ⟨contMDiffAt_id, hB⟩
  simpa [TotalSpace.mk'] using htotal.contMDiffWithinAt

end PoincareConjecture.ConnectionExistence
