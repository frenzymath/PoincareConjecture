import PoincareConjecture.Proofs.M65.Sec19_6_Transfer.ImmersedPerturbationLocal
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.CircleRelabeling











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65Perturbation

local notation "ang" => (fun x : ℝ =>
  (Subtype.mk (Proofs.M58.angularPoint x) (Proofs.M58.norm_angularPoint x) : LoopCircle))

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] in
private theorem velocity_eq_of_angular_eq (gamma : C1FreeLoopSpace (M := M))
    (x y : ℝ) (hxy : ang x = ang y) :
    (curveVelocity (n := 3) (periodicFreeLoop gamma) x : LoopAmbient) =
      curveVelocity (n := 3) (periodicFreeLoop gamma) y := by
  have h := (m65PeriodicLoopTangent_eq gamma x).trans
    ((congrArg (c1LoopTangent gamma) hxy).trans (m65PeriodicLoopTangent_eq gamma y).symm)
  exact congrArg (fun v : TangentBundle (𝓡 3) M => (v.2 : LoopAmbient)) h




theorem exists_circle_neighborhood
    (Gamma : P → ℝ → C1FreeLoopSpace (M := M)) (J : Set ℝ) (d : ℝ)
    (hJ : IsOpen J) (hd : 0 < d)
    (hGamma : ContMDiffOn 𝓘(ℝ, (ℝ × P) × ℝ) (𝓡 3) 1
      (fun z => periodicFreeLoop (Gamma z.1.2 z.2) z.1.1)
      ((univ ×ˢ ball 0 d) ×ˢ J))
    (x q : ℝ) (hq : q ∈ J)
    (hregular : curveVelocity (n := 3) (periodicFreeLoop (Gamma 0 q)) x ≠ 0) :
    ∃ (V : Set P) (A : Set LoopCircle) (T : Set ℝ),
      IsOpen V ∧ 0 ∈ V ∧ IsOpen A ∧ ang x ∈ A ∧ IsOpen T ∧ q ∈ T ∧
      ∀ p ∈ V, ∀ t ∈ T,
        InjOn (Gamma p t : LoopCircle → M) A ∧
        ∀ y : ℝ, ang y ∈ A →
          curveVelocity (n := 3) (periodicFreeLoop (Gamma p t)) y ≠ 0 := by
  obtain ⟨W, hW, hw, _, hvel, hinj⟩ := exists_angular_neighborhood
    (fun z : (ℝ × P) × ℝ => periodicFreeLoop (Gamma z.1.2 z.2) z.1.1)
    ((univ ×ˢ ball 0 d) ×ˢ J) ((isOpen_univ.prod isOpen_ball).prod hJ)
    hGamma ((x, 0), q) ⟨⟨mem_univ _, mem_ball_self hd⟩, hq⟩ hregular
  obtain ⟨B, T, hB, hxB, hT, hqT, hBT⟩ :=
    mem_nhds_prod_iff'.mp (hW.mem_nhds hw)
  obtain ⟨I, V, hI, hxI, hV, hzero, hIV⟩ :=
    mem_nhds_prod_iff'.mp (hB.mem_nhds hxB)
  have hA : IsOpen (ang '' I) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨y, hy, rfl⟩
    rw [← m65AngularCircle_map_nhds y]
    exact image_mem_map (hI.mem_nhds hy)
  refine ⟨V, ang '' I, T, hV, hzero, hA, ⟨x, hxI, rfl⟩, hT, hqT, ?_⟩
  intro p hp t ht
  have hmem (y : ℝ) (hy : y ∈ I) : ((y, p), t) ∈ W := hBT ⟨hIV ⟨hy, hp⟩, ht⟩
  constructor
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ heq
    have hperiod : periodicFreeLoop (Gamma p t) y = periodicFreeLoop (Gamma p t) z :=
      ((Gamma p t).boundary (ang y)).trans (heq.trans ((Gamma p t).boundary (ang z)).symm)
    exact congrArg ang (hinj p t (hmem y hy) (hmem z hz) hperiod)
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hnonzero := hvel ((z, p), t) (hmem z hz)
    rw [← velocity_eq_of_angular_eq (Gamma p t) z y hzy]
    exact hnonzero

set_option maxHeartbeats 800000 in






theorem exists_uniform_immersion_separation
    (Gamma : P → ℝ → C1FreeLoopSpace (M := M)) (J K : Set ℝ) (d : ℝ)
    (hJ : IsOpen J) (hd : 0 < d) (hK : IsCompact K) (hKJ : K ⊆ J)
    (hGamma : ContMDiffOn 𝓘(ℝ, (ℝ × P) × ℝ) (𝓡 3) 1
      (fun z => periodicFreeLoop (Gamma z.1.2 z.2) z.1.1)
      ((univ ×ˢ ball 0 d) ×ˢ J))
    (hregular : ∀ t ∈ K, ∀ x : ℝ,
      curveVelocity (n := 3) (periodicFreeLoop (Gamma 0 t)) x ≠ 0) :
    ∃ delta rho : ℝ, 0 < delta ∧ delta ≤ d ∧ 0 < rho ∧
      ∀ p ∈ ball (0 : P) delta, ∀ t ∈ K,
        (∀ x : ℝ, curveVelocity (n := 3) (periodicFreeLoop (Gamma p t)) x ≠ 0) ∧
        ∀ x y : LoopCircle, dist x y < rho → Gamma p t x = Gamma p t y → x = y := by
  classical
  let S : Set (LoopCircle × ℝ) := univ ×ˢ K
  have hS : IsCompact S := isCompact_univ.prod hK
  have hlocal (z : S) : ∃ (V : Set P) (A : Set LoopCircle) (T : Set ℝ),
      IsOpen V ∧ 0 ∈ V ∧ IsOpen A ∧ z.1.1 ∈ A ∧ IsOpen T ∧ z.1.2 ∈ T ∧
      ∀ p ∈ V, ∀ t ∈ T, InjOn (Gamma p t : LoopCircle → M) A ∧
        ∀ y : ℝ, ang y ∈ A →
          curveVelocity (n := 3) (periodicFreeLoop (Gamma p t)) y ≠ 0 := by
    obtain ⟨x, hx⟩ := m65AngularCircle_surjective z.1.1
    obtain ⟨V, A, T, hV, hpV, hA, hxA, hT, htT, hrest⟩ :=
      exists_circle_neighborhood Gamma J d hJ hd hGamma x z.1.2 (hKJ z.2.2)
        (hregular z.1.2 z.2.2 x)
    exact ⟨V, A, T, hV, hpV, hA, hx ▸ hxA, hT, htT, hrest⟩
  choose V A T hV hpV hA hxA hT htT hcontrol using hlocal
  have hcover : S ⊆ ⋃ z : S, A z ×ˢ T z := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hxA ⟨z, hz⟩, htT ⟨z, hz⟩⟩
  obtain ⟨L, hL⟩ := hS.elim_finite_subcover (fun z : S => A z ×ˢ T z)
    (fun z => (hA z).prod (hT z)) hcover
  have hparams : ∀ᶠ p in 𝓝 (0 : P), ∀ z ∈ L, p ∈ V z :=
    (eventually_all_finset L).mpr (fun z _ => (hV z).mem_nhds (hpV z))
  obtain ⟨eps, heps, hepsV⟩ := Metric.mem_nhds_iff.mp hparams
  have hfinite_cover : S ⊆ ⋃ z : {z // z ∈ L}, A z.1 ×ˢ T z.1 := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp (hL hz)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  obtain ⟨rho, hrho, hLebesgue⟩ := lebesgue_number_lemma_of_metric hS
    (fun z : {z // z ∈ L} => (hA z.1).prod (hT z.1)) hfinite_cover
  refine ⟨min eps d, rho, lt_min heps hd, min_le_right _ _, hrho, ?_⟩
  intro p hp t ht
  have hpVall : ∀ z ∈ L, p ∈ V z :=
    hepsV (ball_subset_ball (min_le_left _ _) hp)
  constructor
  · intro x
    obtain ⟨i, hi⟩ := hLebesgue (ang x, t) ⟨mem_univ _, ht⟩
    have hbase := hi (mem_ball_self hrho)
    exact (hcontrol i.1 p (hpVall i.1 i.2) t hbase.2).2 x hbase.1
  · intro x y hxy heq
    obtain ⟨i, hi⟩ := hLebesgue (x, t) ⟨mem_univ _, ht⟩
    have hx := hi (mem_ball_self hrho)
    have hy : (y, t) ∈ A i.1 ×ˢ T i.1 := by
      apply hi
      simpa only [mem_ball, Prod.dist_eq, dist_self, max_eq_left (dist_nonneg), dist_comm]
        using hxy
    exact (hcontrol i.1 p (hpVall i.1 i.2) t hx.2).1 hx.1 hy.1 heq

end PoincareConjecture.M65Perturbation
