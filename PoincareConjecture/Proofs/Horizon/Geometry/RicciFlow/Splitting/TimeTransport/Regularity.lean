import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.TimeTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.BoundaryRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Frame.Transport.HigherRegularity












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

omit [IsManifold (𝓡 n) ∞ M] in
private lemma contMDiffWithinAt_clm_of_apply
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ E]
    {f : ℝ × M → E →L[ℝ] G} {S : Set (ℝ × M)} {p : ℝ × M}
    (hf : ∀ v, ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, G) ∞
      (fun q => f q v) S p) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E →L[ℝ] G) ∞ f S p := by
  let d := Module.finrank ℝ E
  let e₁ : E ≃L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let e₂ := (e₁.arrowCongr (1 : G ≃L[ℝ] G)).trans
    (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt p
    (contMDiffWithinAt_pi_space.mpr fun i => hf _)

private lemma contMDiffWithinAt_derivWithin_time
    {J : Set ℝ} {f : ℝ × M → ℝ} {t : ℝ} {x : M} (ht : t ∈ J)
    (hJ : UniqueDiffOn ℝ J)
    (hf : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ f
      (J ×ˢ univ) (t, x)) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => derivWithin (fun s => f (s, p.2)) J p.1)
      (J ×ˢ univ) (t, x) := by
  have hc : ContMDiffWithinAt ((𝓘(ℝ, ℝ).prod (𝓡 n)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : (ℝ × M) × ℝ => f (p.2, p.1.2))
      ((J ×ˢ univ) ×ˢ J) ((t, x), t) := by
    exact hf.comp_of_eq (contMDiffWithinAt_snd.prodMk
      (contMDiffWithinAt_snd.comp _ contMDiffWithinAt_fst (fun _ _ => mem_univ _)))
      (fun p hp => ⟨hp.2, mem_univ _⟩) rfl
  have hd := hc.mfderivWithin (f := fun p s => f (s, p.2))
    (g := Prod.fst) contMDiffWithinAt_fst
    (show (t, x) ∈ J ×ˢ (univ : Set M) from ⟨ht, mem_univ _⟩)
    (fun p hp => hp.1) (m := ∞) (by simp) hJ.uniqueMDiffOn
  have h := hd.clm_apply (contMDiffWithinAt_const (c := (1 : ℝ)))
  convert h using 1
  funext p
  rw [inTangentCoordinates_model_space]
  simp only [mfderivWithin_eq_fderivWithin, derivWithin]

theorem contMDiffWithinAt_ricci_fields
    (hab : a < b) (F : RicciFlow n M (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b) {x : M}
    {X Y : (y : M) → TangentSpace (𝓡 n) y}
    (hX : ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.connection p.1).ricci p.2 (X p.2) (Y p.2))
      (Icc a b ×ˢ univ) (t, x) := by
  have h := contMDiffWithinAt_derivWithin_time ht (uniqueDiffOn_Icc hab)
    (F.contMDiffWithinAt_inner_fields ht hX hY)
  apply (h.div_const (-2 : ℝ)).congr_of_eventuallyEq_of_mem
    (hx := show (t, x) ∈ Icc a b ×ˢ (univ : Set M) from ⟨ht, mem_univ _⟩)
  filter_upwards [self_mem_nhdsWithin] with p hp
  rw [(F.equation p.1 hp.1 p.2 (X p.2) (Y p.2)).derivWithin
    (uniqueDiffOn_Icc hab p.1 hp.1)]
  ring

theorem contMDiffWithinAt_ricciEndomorphism_inCoordinates
    (hab : a < b) (F : RicciFlow n M (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b) (x : M) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      (fun p : ℝ × M => ContinuousLinearMap.inCoordinates
        (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
        (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
        x p.2 x p.2 (ricciEndomorphism F p.2 p.1))
      (Icc a b ×ˢ univ) (t, x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  let e' := trivializationAt (E →L[ℝ] ℝ) (fun y => V y →L[ℝ] ℝ) x
  let G (p : ℝ × M) := ContinuousLinearMap.inCoordinates E V (E →L[ℝ] ℝ)
    (fun y => V y →L[ℝ] ℝ) x p.2 x p.2 ((F.metric p.1).inner p.2)
  let R (p : ℝ × M) := ContinuousLinearMap.inCoordinates E V (E →L[ℝ] ℝ)
    (fun y => V y →L[ℝ] ℝ) x p.2 x p.2 (ricciForm F p.2 p.1)
  have hG : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ G (Icc a b ×ˢ univ) (t, x) :=
    (contMDiffWithinAt_hom_bundle _).mp (F.smooth (t, x) ⟨ht, mem_univ _⟩) |>.2
  have hR : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ R (Icc a b ×ˢ univ) (t, x) := by
    apply contMDiffWithinAt_clm_of_apply
    intro v
    apply contMDiffWithinAt_clm_of_apply
    intro w
    have hfield (z : E) : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
        (fun y => TotalSpace.mk' E y (e.symmL ℝ y z)) x := by
      have hz : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
          (fun y => TotalSpace.mk' E y z) x := by
        rw [contMDiffAt_totalSpace]
        exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const (c := z)⟩
      exact (e.contMDiffAt_symmL (IB := 𝓡 n) (n := ∞)
        (FiberBundle.mem_baseSet_trivializationAt E V x)).clm_bundle_apply hz
    have h := contMDiffWithinAt_ricci_fields hab F ht (hfield v) (hfield w)
    apply h.congr_of_eventuallyEq_of_mem (hx := ⟨ht, mem_univ x⟩)
    have he' : ∀ᶠ p : ℝ × M in 𝓝[Icc a b ×ˢ univ] (t, x),
        p.2 ∈ e'.baseSet :=
      continuousAt_snd.continuousWithinAt.eventually
        (e'.open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ)
            (fun y => V y →L[ℝ] ℝ) x))
    filter_upwards [he', self_mem_nhdsWithin] with p hp hpJ
    dsimp only [R]
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
    rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hp]
    change (ContinuousLinearMap.inCoordinates E V ℝ (fun _ : M => ℝ)
      x p.2 x p.2 (ricciForm F p.2 p.1 (e.symmL ℝ p.2 v))) w = _
    have hetriv : trivializationAt ℝ (fun _ : M => ℝ) x =
        Bundle.Trivial.trivialization M ℝ := rfl
    simp only [ContinuousLinearMap.inCoordinates, hetriv,
      ContinuousLinearMap.comp_apply, Bundle.Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.id_apply]
    exact ricciForm_apply hab F p.2 hpJ.1 _ _
  have hGinv (p : ℝ × M) (hp : p.2 ∈ e.baseSet) (hp' : p.2 ∈ e'.baseSet) :
      (G p).IsInvertible := by
    dsimp only [G]
    rw [ContinuousLinearMap.inCoordinates_eq hp hp']
    exact ContinuousLinearMap.isInvertible_equiv.comp
      (((F.metric p.1).inner_isInvertible p.2).comp ContinuousLinearMap.isInvertible_equiv)
  have hinv := (hGinv (t, x) (FiberBundle.mem_baseSet_trivializationAt E V x)
    (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ)
      (fun y => V y →L[ℝ] ℝ) x)).contDiffAt_map_inverse (n := ∞)
  have h := (hinv.contMDiffAt.comp_contMDiffWithinAt (t, x) hG).clm_comp hR
  apply h.congr_of_eventuallyEq_of_mem (hx := ⟨ht, mem_univ x⟩)
  have he : ∀ᶠ p : ℝ × M in 𝓝[Icc a b ×ˢ univ] (t, x),
      p.2 ∈ e.baseSet ∧ p.2 ∈ e'.baseSet := by
    apply (continuousAt_snd : ContinuousAt (Prod.snd : ℝ × M → M) (t, x)).continuousWithinAt.eventually
      (p := fun y => y ∈ e.baseSet ∧ y ∈ e'.baseSet)
    exact inter_mem (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E V x))
      (e'.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt (E →L[ℝ] ℝ)
        (fun y => V y →L[ℝ] ℝ) x))
  filter_upwards [he] with p hp
  apply ContinuousLinearMap.ext
  intro v
  symm
  apply (hGinv p hp.1 hp.2).inverse_apply_eq.mpr
  symm
  dsimp only [G, R]
  rw [ContinuousLinearMap.inCoordinates_eq hp.1 hp.2,
    ContinuousLinearMap.inCoordinates_eq hp.1 hp.1,
    ContinuousLinearMap.inCoordinates_eq hp.1 hp.2]
  change (e'.continuousLinearEquivAt ℝ p.2 hp.2)
    ((F.metric p.1).inner p.2
      ((e.continuousLinearEquivAt ℝ p.2 hp.1).symm
        ((e.continuousLinearEquivAt ℝ p.2 hp.1)
          (((F.metric p.1).inner p.2).inverse
            (ricciForm F p.2 p.1 ((e.continuousLinearEquivAt ℝ p.2 hp.1).symm v)))))) =
      (e'.continuousLinearEquivAt ℝ p.2 hp.2)
        (ricciForm F p.2 p.1 ((e.continuousLinearEquivAt ℝ p.2 hp.1).symm v))
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [((F.metric p.1).inner_isInvertible p.2).self_apply_inverse]

theorem contMDiffOn_ricciEndomorphism
    (hab : a < b) (F : RicciFlow n M (Icc a b)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (E := fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
        p.2 (ricciEndomorphism F p.2 p.1)) (Icc a b ×ˢ univ) := by
  intro p hp
  rw [contMDiffWithinAt_hom_bundle]
  exact ⟨contMDiffWithinAt_snd,
    contMDiffWithinAt_ricciEndomorphism_inCoordinates hab F hp.1 p.2⟩

theorem contMDiffWithinAt_ricciEndomorphism_inCoordinates_of_mem
    (hab : a < b) (F : RicciFlow n M (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b)
    (x : M) {y : M}
    (hy : y ∈ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).baseSet) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ∞
      (fun p : ℝ × M => ContinuousLinearMap.inCoordinates
        (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
        (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
        x p.2 x p.2 (ricciEndomorphism F p.2 p.1))
      (Icc a b ×ˢ univ) (t, y) := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt (E →L[ℝ] E)
    (fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y) x
  have hm : (TotalSpace.mk' (E →L[ℝ] E) y (ricciEndomorphism F y t)) ∈ e.source := by
    change y ∈ (trivializationAt E (TangentSpace (𝓡 n)) x).baseSet ∩
      (trivializationAt E (TangentSpace (𝓡 n)) x).baseSet
    exact ⟨hy, hy⟩
  exact (e.contMDiffWithinAt_iff
    (f := fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun y : M => TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) y)
      p.2 (ricciEndomorphism F p.2 p.1)) (x₀ := (t, y)) hm).mp
    (contMDiffOn_ricciEndomorphism hab F (t, y) ⟨ht, mem_univ y⟩) |>.2

noncomputable def chartRicciCoefficient (F : RicciFlow n M (Icc a b)) (x : M)
    (z : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  let y := (extChartAt (𝓡 n) x).symm z
  ContinuousLinearMap.inCoordinates
    (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
    (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))
    x y x y (ricciEndomorphism F y t)

theorem chartRicciCoefficient_contDiffOn
    (hab : a < b) (F : RicciFlow n M (Icc a b)) (x : M) :
    ContDiffOn ℝ ∞ (Function.uncurry (chartRicciCoefficient F x))
      ((extChartAt (𝓡 n) x).target ×ˢ Icc a b) := by
  rintro ⟨z, t⟩ ⟨hz, ht⟩
  have hz' : (extChartAt (𝓡 n) x).symm z ∈
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    simpa only [extChartAt_source] using (extChartAt (𝓡 n) x).map_target hz
  have harg : ContMDiffWithinAt
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ => (p.2, (extChartAt (𝓡 n) x).symm p.1))
      ((extChartAt (𝓡 n) x).target ×ˢ Icc a b) (z, t) :=
    contMDiffWithinAt_snd.prodMk
      (((contMDiffOn_extChartAt_symm x) z hz).comp (z, t) contMDiffWithinAt_fst mapsTo_fst_prod)
  have h := (contMDiffWithinAt_ricciEndomorphism_inCoordinates_of_mem hab F ht x hz').comp
    (z, t) harg
    (show MapsTo (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      (p.2, (extChartAt (𝓡 n) x).symm p.1))
      ((extChartAt (𝓡 n) x).target ×ˢ Icc a b) (Icc a b ×ˢ univ) from
      fun p hp => ⟨hp.2, mem_univ _⟩)
  simp +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffWithinAt

end PoincareConjecture.RicciFlow.Splitting
