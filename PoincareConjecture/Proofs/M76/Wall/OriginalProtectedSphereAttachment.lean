import PoincareConjecture.Proofs.M76.Wall.OriginalTwoSphereArcAttachment
import PoincareConjecture.Proofs.M76.Wall.SphericalFrontierFilling

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem ChartwisePLSphere.exists_mem_ne
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (a : X) : ∃ x ∈ S, x ≠ a := by
  let u : sphere (0 : V3) 1 := ⟨fun _ => 1, by
    simp only [mem_sphere, dist_zero_right, pi_norm_const, Real.norm_eq_abs, abs_one]⟩
  let v : sphere (0 : V3) 1 := ⟨fun _ => -1, by
    simp only [mem_sphere, dist_zero_right, pi_norm_const, Real.norm_eq_abs, abs_neg, abs_one]⟩
  have huv : u ≠ v := by
    intro h
    have hc := congrFun (congrArg Subtype.val h) (0 : Fin 3)
    change (1 : ℝ) = -1 at hc
    norm_num at hc
  have hdiff : (s.parametrization u : X) ≠ (s.parametrization v : X) := by
    intro h
    exact huv (s.parametrization.injective (Subtype.ext h))
  by_cases hu : (s.parametrization u : X) = a
  · exact ⟨s.parametrization v, (s.parametrization v).property,
      fun hv => hdiff (hu.trans hv.symm)⟩
  · exact ⟨s.parametrization u, (s.parametrization u).property, hu⟩

theorem PLDomain.exists_protected_two_sphere_attachment
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L : Set X}
    (he : PLDomain e L) (hL : IsCompact L) (hconn : IsConnected L)
    {q : ℝ → X} (hq : PolyhedralPLInCharts e q I) (hqi : InjOn q I)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∉ L)
    (S : Fin 2 → Set X) (hsphere : ∀ i, ChartwisePLSphere e (S i))
    (hSL : ∀ i, S i ⊆ frontier L)
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (hzero : q 0 ∈ S 0) (hone : q 1 ∈ S 1)
    {B P O : Set X} (hB : IsClosed B) (hP : IsClosed P)
    (hfront : frontier L = B ∪ (S 0 ∪ S 1)) (hBS : ∀ i, Disjoint B (S i))
    (hprotect : Disjoint P (q '' I)) (hO : IsOpen O) (hqO : MapsTo q I O) :
    ∃ Lnew Snew : Set X, IsCompact Lnew ∧ IsConnected Lnew ∧ L ⊆ Lnew ∧
      Lnew \ L ⊆ O \ P ∧ PLDomain e Lnew ∧
      Nonempty (ChartwisePLSphere e Snew) ∧
      frontier Lnew = B ∪ Snew ∧ Disjoint B Snew ∧
      ∃ V : Set X, IsOpen V ∧ P ⊆ V ∧ V ∩ Lnew = V ∩ L := by
  classical
  let endpoint : Fin 2 → X := Fin.cases (q 0) (fun _ => q 1)
  choose x hxS hxne using fun i => (hsphere i).exists_mem_ne (endpoint i)
  have hSclosed (i : Fin 2) : IsClosed (S i) := (hsphere i).compact_connected.1.isClosed
  have hS01 : Disjoint (S 0) (S 1) := hdisjoint (by decide)
  have hBL : B ⊆ L := fun _ hb =>
    he.closed.frontier_subset (hfront.symm.subset (Or.inl hb))
  have hqB : Disjoint B (q '' I) := by
    apply disjoint_left.mpr
    rintro y hyB ⟨t, ht, rfl⟩
    by_cases ht0 : t = 0
    · subst t
      exact disjoint_left.mp (hBS 0) hyB hzero
    by_cases ht1 : t = 1
    · subst t
      exact disjoint_left.mp (hBS 1) hyB hone
    exact hproper t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩ (hBL hyB)
  have hpointAvoid (i : Fin 2) : x i ∉ q '' I := by
    rintro ⟨t, ht, htx⟩
    by_cases ht0 : t = 0
    · subst t
      fin_cases i
      · exact hxne 0 htx.symm
      · exact disjoint_left.mp hS01 hzero (htx.symm ▸ hxS 1)
    by_cases ht1 : t = 1
    · subst t
      fin_cases i
      · exact disjoint_left.mp hS01 (htx.symm ▸ hxS 0) hone
      · exact hxne 1 htx.symm
    apply hproper t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    rw [htx]
    exact he.closed.frontier_subset (hSL i (hxS i))
  let bad : Set X := (P ∪ B) ∪ {x 0, x 1}
  have hbad : IsClosed bad :=
    (hP.union hB).union (((finite_singleton (x 1)).insert (x 0)).isClosed)
  let W : Set X := O ∩ badᶜ
  have hW : IsOpen W := hO.inter hbad.isOpen_compl
  have hqW : MapsTo q I W := by
    intro t ht
    refine ⟨hqO ht, ?_⟩
    rintro ((htP | htB) | htpoint)
    · exact disjoint_left.mp hprotect htP (mem_image_of_mem q ht)
    · exact disjoint_left.mp hqB htB (mem_image_of_mem q ht)
    · rcases mem_insert_iff.mp htpoint with ht0 | ht1
      · exact hpointAvoid 0 ⟨t, ht, ht0⟩
      · exact hpointAvoid 1 ⟨t, ht, mem_singleton_iff.mp ht1⟩
  have hBW : Disjoint B W := by
    apply disjoint_left.mpr
    exact fun _ hb hw => hw.2 (Or.inl (Or.inr hb))
  have hout (i : Fin 2) : (S i \ W).Nonempty := by
    refine ⟨x i, hxS i, ?_⟩
    intro hxW
    apply hxW.2
    apply Or.inr
    fin_cases i
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ (mem_singleton _)
  let U : Fin 2 → Set X := Fin.cases (B ∪ S 1)ᶜ (fun _ => (B ∪ S 0)ᶜ)
  have hU (i : Fin 2) : IsOpen (U i) := by
    fin_cases i
    · exact (hB.union (hSclosed 1)).isOpen_compl
    · exact (hB.union (hSclosed 0)).isOpen_compl
  have hU0 : q 0 ∈ U 0 := by
    rintro (hb | hs)
    · exact disjoint_left.mp (hBS 0) hb hzero
    · exact disjoint_left.mp hS01 hzero hs
  have hU1 : q 1 ∈ U 1 := by
    rintro (hb | hs)
    · exact disjoint_left.mp (hBS 1) hb hone
    · exact disjoint_left.mp hS01 hs hone
  have hUS (i : Fin 2) : U i ∩ frontier L ⊆ S i := by
    intro y hy
    rcases hfront.subset hy.2 with hb | hs0 | hs1
    · fin_cases i
      · exact False.elim (hy.1 (Or.inl hb))
      · exact False.elim (hy.1 (Or.inl hb))
    · fin_cases i
      · exact hs0
      · exact False.elim (hy.1 (Or.inr hs0))
    · fin_cases i
      · exact False.elim (hy.1 (Or.inr hs1))
      · exact hs1
  obtain ⟨R, Snew, hRc, hRconn, hRW, _, hnew, hSphere, hfr, hdisj, hinter⟩ :=
    he.exists_two_sphere_arc_attachment hL hq hqi hproper S hsphere hSL hdisjoint
      hzero hone hfront hBS hW hqW hBW hout U hU hU0 hU1 hUS
  refine ⟨L ∪ R, Snew, hL.union hRc, IsConnected.union hinter hconn hRconn,
    subset_union_left, ?_, hnew, hSphere, hfr, hdisj, Rᶜ, hRc.isClosed.isOpen_compl, ?_, ?_⟩
  · rintro y ⟨hyL | hyR, hyold⟩
    · exact False.elim (hyold hyL)
    · exact ⟨(hRW hyR).1, fun hyP => (hRW hyR).2 (Or.inl (Or.inl hyP))⟩
  · intro y hyP hyR
    exact (hRW hyR).2 (Or.inl (Or.inl hyP))
  · simp only [inter_union_distrib_left, compl_inter_self, union_empty]

end PoincareConjecture.M76
