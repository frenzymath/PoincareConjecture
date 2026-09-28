import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.TimeTransport.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

private theorem linearODE_contDiffOn_terminal
    {P G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (A : P → ℝ → G →L[ℝ] G) {a b : ℝ} (hab : a ≤ b)
    {U : Set P} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ Icc a b))
    (Φ : P → ℝ → G) (hterm : ContDiffOn ℝ ∞ (fun p => Φ p b) U)
    (hsol : ∀ p ∈ U, ∀ t ∈ Icc a b,
      HasDerivWithinAt (Φ p) (A p t (Φ p t)) (Icc a b) t) :
    ContDiffOn ℝ ∞ (Function.uncurry Φ) (U ×ˢ Icc a b) := by
  let A' : P → ℝ → G →L[ℝ] G := fun p t => -A p (-t)
  let Φ' : P → ℝ → G := fun p t => Φ p (-t)
  have hmap : MapsTo (fun q : P × ℝ => (q.1, -q.2))
      (U ×ˢ Icc (-b) (-a)) (U ×ˢ Icc a b) := by
    intro q hq
    exact ⟨hq.1, by constructor <;> linarith [hq.2.1, hq.2.2]⟩
  have hA' : ContDiffOn ℝ ∞ (Function.uncurry A') (U ×ˢ Icc (-b) (-a)) :=
    (hA.comp (contDiff_fst.prodMk contDiff_snd.neg).contDiffOn hmap).neg
  have hterm' : ContDiffOn ℝ ∞ (fun p => Φ' p (-b)) U := by
    simpa only [Φ', neg_neg] using hterm
  have hsol' : ∀ p ∈ U, ∀ t ∈ Icc (-b) (-a),
      HasDerivWithinAt (Φ' p) (A' p t (Φ' p t)) (Icc (-b) (-a)) t := by
    intro p hp t ht
    have hnt : -t ∈ Icc a b := by constructor <;> linarith [ht.1, ht.2]
    have h := (hsol p hp (-t) hnt).scomp t
      (hasDerivWithinAt_id t (Icc (-b) (-a))).neg
      (show MapsTo (fun s : ℝ => -s) (Icc (-b) (-a)) (Icc a b) from
        fun s hs => by constructor <;> linarith [hs.1, hs.2])
    simpa only [Φ', A', Function.comp_def, neg_smul, one_smul,
      neg_apply] using h
  have h := Frame.linearODE_contDiffOn A' (neg_le_neg hab) hU hA' Φ' hterm' hsol'
  have hmap' : MapsTo (fun q : P × ℝ => (q.1, -q.2))
      (U ×ˢ Icc a b) (U ×ˢ Icc (-b) (-a)) :=
    fun q hq => ⟨hq.1, neg_le_neg hq.2.2, neg_le_neg hq.2.1⟩
  simpa only [Function.comp_def, Function.uncurry_def, Φ', neg_neg] using
    h.comp (contDiff_fst.prodMk contDiff_snd.neg).contDiffOn hmap'

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem ricci_transport_contMDiffOn
    (hab : a < b) (F : RicciFlow n M (Icc a b))
    (X : ℝ → (x : M) → TangentSpace (𝓡 n) x)
    (hXb : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X b)))
    (hode : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨(F.metric b).toRiemannianMetric⟩
      ∀ x : M, ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => X s x)
        (ricciSharp (F.connection t) x (X t x)) (Icc a b) t) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (Icc a b ×ˢ univ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  rintro ⟨t, x⟩ ⟨ht, _⟩
  let E := EuclideanSpace ℝ (Fin n)
  let e := extChartAt (𝓡 n) x
  let v := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) x
  let Φ : E → ℝ → E := fun z s =>
    (v (TotalSpace.mk' E (e.symm z) (X s (e.symm z)))).2
  have hzbase (z : E) (hz : z ∈ e.target) : e.symm z ∈ v.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    simpa only [e, extChartAt_source] using e.map_target hz
  have hterm : ContDiffOn ℝ ∞ (fun z => Φ z b) e.target := by
    intro z hz
    have h := (v.contMDiffAt_iff (f := T% (X b)) (x₀ := e.symm z)
      (show TotalSpace.mk' E (e.symm z) (X b (e.symm z)) ∈ v.source from
        hzbase z hz)).mp (hXb (e.symm z)) |>.2
    exact (h.comp_contMDiffWithinAt z (contMDiffOn_extChartAt_symm x z hz)).contDiffWithinAt
  have hsol : ∀ z ∈ e.target, ∀ s ∈ Icc a b,
      HasDerivWithinAt (Φ z)
        (chartRicciCoefficient F x z s (Φ z s)) (Icc a b) s := by
    intro z hz s hs
    let y := e.symm z
    let : NormedAddCommGroup (TangentSpace (𝓡 n) y) := inferInstance
    let : NormedSpace ℝ (TangentSpace (𝓡 n) y) := inferInstance
    let c := v.continuousLinearEquivAt ℝ y (hzbase z hz)
    have hc (r : ℝ) : Φ z r = c (X r y) := by
      simp only [c, Trivialization.continuousLinearEquivAt_apply, Φ, y]
    have hd := c.hasFDerivAt.comp_hasDerivWithinAt s (hode y s hs)
    have heq : chartRicciCoefficient F x z s (Φ z s) =
        c (ricciSharp (F.connection s) y (X s y)) := by
      dsimp only [chartRicciCoefficient]
      rw [ContinuousLinearMap.inCoordinates_eq (hzbase z hz) (hzbase z hz), hc s]
      change c (ricciEndomorphism F y s (c.symm (c (X s y)))) = _
      rw [c.symm_apply_apply, ricciEndomorphism_eq_ricciSharp hab F y hs]
    rw [heq]
    exact hd.congr (fun r _ => hc r) (hc s)
  have hchart := linearODE_contDiffOn_terminal (chartRicciCoefficient F x) hab.le
    (isOpen_extChartAt_target x) (chartRicciCoefficient_contDiffOn hab F x) Φ hterm hsol
  rw [contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  let S : Set (ℝ × M) := Icc a b ×ˢ e.source
  have harg : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × M => (e p.2, p.1)) S (t, x) :=
    ((contMDiffAt_extChartAt (I := 𝓡 n) (x := x)).comp (t, x)
      contMDiffAt_snd).contMDiffWithinAt.prodMk contMDiffWithinAt_fst
  have hmap : MapsTo (fun p : ℝ × M => (e p.2, p.1)) S (e.target ×ˢ Icc a b) :=
    fun p hp => ⟨e.map_source hp.2, hp.1⟩
  have hc₀ : ContMDiffWithinAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) ∞
      (Function.uncurry Φ) (e.target ×ˢ Icc a b) (e x, t) :=
    (hchart (e x, t) ⟨mem_extChartAt_target x, ht⟩).contMDiffWithinAt
  have hc : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E) ∞
      ((Function.uncurry Φ) ∘ (fun p : ℝ × M => (e p.2, p.1))) S (t, x) := by
    apply hc₀.comp (t, x) (f := fun p : ℝ × M => (e p.2, p.1)) _ hmap
    simpa +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] using harg
  have hS : S ∈ 𝓝[Icc a b ×ˢ univ] (t, x) := by
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨univ ×ˢ e.source,
      (isOpen_univ.prod (isOpen_extChartAt_source (I := 𝓡 n) x)).mem_nhds
        ⟨mem_univ _, mem_extChartAt_source x⟩, ?_⟩
    intro p hp
    exact ⟨hp.2.1, hp.1.2⟩
  apply (hc.mono_of_mem_nhdsWithin hS).congr_of_eventuallyEq
  · filter_upwards [hS] with p hp
    exact congrArg (fun y => (v (TotalSpace.mk' E y (X p.1 y))).2)
      (e.left_inv hp.2).symm
  · exact congrArg (fun y => (v (TotalSpace.mk' E y (X t y))).2)
      (e.left_inv (mem_extChartAt_source x)).symm

theorem exists_smooth_terminal_ricci_transport_field
    (hC : RicciFlowCurvatureTheory.{u}) (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (Xb : (x : M) → TangentSpace (𝓡 n) x)
    (hXb : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Xb)) :
    ∃ X : ℝ → (x : M) → TangentSpace (𝓡 n) x,
      X b = Xb ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
        (Icc a b ×ˢ univ) ∧
      (letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
          ⟨(F.metric b).toRiemannianMetric⟩
        ∀ x : M, ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => X s x)
          (ricciSharp (F.connection t) x (X t x)) (Icc a b) t) ∧
      ∀ t ∈ Icc a b, ∀ x : M,
        (F.metric t).inner x (X t x) (X t x) = (F.metric b).inner x (Xb x) (Xb x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric b).toRiemannianMetric⟩
  choose U hUb hUd hUp hUi using exists_terminal_ricci_transport hC hab F
  let X : ℝ → (x : M) → TangentSpace (𝓡 n) x := fun t x => U x t (Xb x)
  have hterminal : X b = Xb := by
    funext x
    change U x b (Xb x) = Xb x
    rw [hUb x, ContinuousLinearMap.id_apply]
  have hode : ∀ x : M, ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => X s x)
      (ricciSharp (F.connection t) x (X t x)) (Icc a b) t :=
    fun x t ht => hUd x t ht (Xb x)
  refine ⟨X, hterminal, ricci_transport_contMDiffOn hab F X ?_ hode, hode, ?_⟩
  · simpa only [hterminal] using hXb
  · intro t ht x
    exact hUp x t ht (Xb x) (Xb x)

end PoincareConjecture.RicciFlow.Splitting
