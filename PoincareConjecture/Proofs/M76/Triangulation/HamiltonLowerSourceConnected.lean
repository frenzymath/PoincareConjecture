import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLowerOriginalAtlas

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

theorem lower_lattice_puncture_isConnected
    (κ : Type*) [Finite κ] [Nonempty κ] :
    IsConnected ({hamiltonLowerLatticePuncture κ}ᶜ :
      Set ((κ → ℝ) ⧸ (hamiltonLowerPeriodLattice κ).toAddSubgroup)) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  let C := AddCircle (4 * (128 : ℝ))
  let p : C := (256 : ℝ)
  let Q := AddCircle.openPartialHomeomorphCoe (4 * (128 : ℝ)) 256
  have hsource : IsConnected Q.source := by
    change IsConnected (Ioo (256 : ℝ) (256 + 4 * 128))
    exact isConnected_Ioo (by norm_num)
  have hpunct : IsConnected ({p}ᶜ : Set C) := by
    have h := hsource.image Q Q.continuousOn
    rw [Q.image_source_eq_target] at h
    exact h
  have hwhole : IsConnected (univ : Set C) := isConnected_univ
  let s : κ → Set (κ → C) := fun i =>
    pi univ (fun j => if j = i then {p}ᶜ else univ)
  have hs (i : κ) : IsConnected (s i) := by
    apply isConnected_univ_pi.mpr
    intro j
    by_cases hji : j = i
    · simpa only [hji, if_pos rfl, if_true] using hpunct
    · simpa only [if_neg hji] using hwhole
  obtain ⟨y, hy⟩ := hpunct.nonempty
  have hcommon (i : κ) : (fun _ : κ => y) ∈ s i := by
    intro j _
    change y ∈ if j = i then {p}ᶜ else univ
    split_ifs
    · exact hy
    · exact mem_univ _
  have hconn : IsConnected (⋃ i, s i) :=
    ⟨⟨fun _ => y, mem_iUnion.mpr ⟨Classical.arbitrary κ, hcommon _⟩⟩,
      isPreconnected_iUnion ⟨fun _ => y, mem_iInter.mpr hcommon⟩ (fun i => (hs i).isPreconnected)⟩
  have hunion : (⋃ i, s i) = ({fun _ : κ => p}ᶜ : Set (κ → C)) := by
    ext z
    constructor
    · intro hz heq
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      have hzi : z i ≠ p := by
        simpa only [s, mem_pi, mem_univ, forall_const, if_pos rfl, if_true,
          mem_compl_iff, mem_singleton_iff] using
          hi i (mem_univ i)
      exact hzi (congrFun (mem_singleton_iff.mp heq) i)
    · intro hz
      have hne : ∃ i, z i ≠ p := by
        by_contra hn
        push Not at hn
        exact hz (mem_singleton_iff.mpr (funext hn))
      obtain ⟨i, hi⟩ := hne
      refine mem_iUnion.mpr ⟨i, ?_⟩
      intro j _
      change z j ∈ if j = i then {p}ᶜ else univ
      by_cases hji : j = i
      · simpa only [hji, if_pos rfl, if_true, mem_compl_iff, mem_singleton_iff] using hi
      · simp only [if_neg hji, mem_univ]
  rw [hunion] at hconn
  let t := hamiltonLowerLatticePiEquiv κ
  have hp : t (hamiltonLowerLatticePuncture κ) = fun _ : κ => p := rfl
  have hpre : t ⁻¹' ({fun _ : κ => p}ᶜ : Set (κ → C)) =
      {hamiltonLowerLatticePuncture κ}ᶜ := by
    ext z
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, ← hp, t.injective.eq_iff]
  have h := t.isConnected_preimage.mpr hconn
  simpa only [hpre] using h

theorem lower_original_domain_isConnected
    {ι κ : Type*} [Fintype ι] [Finite κ] [Nonempty κ]
    {a b : ℝ} (hb : 1 < b)
    (U : TopologicalSpace.Opens
      (LatticeHandleAmbient ι κ (hamiltonLowerPeriodLattice κ)))
    (hU : (U : Set (LatticeHandleAmbient ι κ (hamiltonLowerPeriodLattice κ))) =
      (ball (0 : ι → ℝ) b ×ˢ {hamiltonLowerLatticePuncture κ}ᶜ) ∪
        ({x : ι → ℝ | a < ‖x‖ ∧ ‖x‖ < b} ×ˢ univ)) :
    IsConnected ((Subtype.val : U → _) ⁻¹'
      latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ)) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  let T := ((κ → ℝ) ⧸ (hamiltonLowerPeriodLattice κ).toAddSubgroup)
  let W := LatticeHandleAmbient ι κ (hamiltonLowerPeriodLattice κ)
  let p := hamiltonLowerLatticePuncture κ
  let : ConnectedSpace T := (hamiltonLowerLatticePiEquiv κ).connectedSpace_iff.mpr inferInstance
  have hpunct : IsConnected ({p}ᶜ : Set T) := lower_lattice_puncture_isConnected κ
  have hball : IsConnected (closedBall (0 : ι → ℝ) 1) :=
    (convex_closedBall (0 : ι → ℝ) 1).isConnected ⟨0, mem_closedBall_self (by norm_num)⟩
  let base : Set W := closedBall (0 : ι → ℝ) 1 ×ˢ {p}ᶜ
  let D : Set W := {z | ‖z.1‖ ≤ 1 ∧ (z.2 ≠ p ∨ a < ‖z.1‖)}
  have hbase : IsConnected base := hball.prod hpunct
  have hbaseD : base ⊆ D :=
    fun _ hz => ⟨mem_closedBall_zero_iff.mp hz.1, Or.inl hz.2⟩
  obtain ⟨y, hy⟩ := hpunct.nonempty
  let z0 : W := (0, y)
  have hz0 : z0 ∈ base := ⟨mem_closedBall_self (by norm_num), hy⟩
  have hD : IsConnected D := by
    refine ⟨⟨z0, hbaseD hz0⟩, isPreconnected_of_forall z0 ?_⟩
    intro z hz
    rcases hz.2 with hzp | hza
    · exact ⟨base, hbaseD, hz0, ⟨mem_closedBall_zero_iff.mpr hz.1, hzp⟩,
        hbase.isPreconnected⟩
    · let fiber : Set W := {z.1} ×ˢ univ
      have hfiber : IsConnected fiber := isConnected_singleton.prod isConnected_univ
      have hinter : (base ∩ fiber).Nonempty :=
        ⟨(z.1, y), ⟨⟨mem_closedBall_zero_iff.mpr hz.1, hy⟩, rfl, mem_univ _⟩⟩
      refine ⟨base ∪ fiber, ?_, Or.inl hz0, Or.inr ⟨rfl, mem_univ _⟩,
        (hbase.union hinter hfiber).isPreconnected⟩
      intro w hw
      rcases hw with hw | hw
      · exact hbaseD hw
      · have hwz : w.1 = z.1 := hw.1
        exact ⟨by simpa only [hwz] using hz.1, Or.inr (by simpa only [hwz] using hza)⟩
  let R : Set U := (Subtype.val : U → W) ⁻¹'
    latticeHandleDomain ι κ (hamiltonLowerPeriodLattice κ)
  have himage : (Subtype.val : U → W) '' R = D := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨mem_closedBall_zero_iff.mp hx.1, ?_⟩
      have hxu := x.property
      change (x : W) ∈ (U : Set W) at hxu
      rw [hU] at hxu
      rcases hxu with hxu | hxu
      · exact Or.inl hxu.2
      · exact Or.inr hxu.1.1
    · intro hz
      have hnorm : ‖z.1‖ < b := hz.1.trans_lt hb
      have hzu : z ∈ (U : Set W) := by
        rw [hU]
        rcases hz.2 with hzp | hza
        · exact Or.inl ⟨mem_ball_zero_iff.mpr hnorm, hzp⟩
        · exact Or.inr ⟨⟨hza, hnorm⟩, mem_univ _⟩
      exact ⟨⟨z, hzu⟩, ⟨mem_closedBall_zero_iff.mpr hz.1, mem_univ _⟩, rfl⟩
  have hpre : IsPreconnected R := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    change IsPreconnected ((Subtype.val : U → W) '' R)
    rw [himage]
    exact hD.isPreconnected
  obtain ⟨z, hz⟩ := hD.nonempty
  rw [← himage] at hz
  obtain ⟨x, hx, _⟩ := hz
  exact ⟨⟨x, hx⟩, hpre⟩

end PoincareConjecture.M76
