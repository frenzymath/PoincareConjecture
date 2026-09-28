import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.DiskBoundaryHomotopy



set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

theorem exists_simple_rim_loops_of_marked_disk_homotopy
    {X : Type*} [TopologicalSpace X] {R S : Set X}
    {d r : Set P2} (hd : IsFinitePLBallPair P2 d r)
    {q k : P2 → X} (hqi : InjOn q d) (hki : InjOn k d)
    (H : C(I × d,R))
    (hH0 : ∀ z : d,(H (0,z) : X)=q z)
    (hH1 : ∀ z : d,(H (1,z) : X)=k z)
    (hHmark : ∀ (t : I) (z : d),(H (t,z) : X) ∈ S ↔ (z : P2) ∈ r) :
    ∃ gamma delta : C(Rim,↥(S ∩ R)),
      Function.Injective gamma ∧ Function.Injective delta ∧
      range (fun z => (gamma z : X)) = q '' r ∧
      range (fun z => (delta z : X)) = k '' r ∧
      gamma.Homotopic delta := by
  have hstd : IsFinitePLBallPair P2 Disk Rim :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  obtain ⟨A,hA,hAr⟩ := hstd.exists_homeomorph hd
  let a : C(Rim,d) := ⟨fun z => A ⟨z,sphere_subset_closedBall z.property⟩,
    A.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
  have hai : Function.Injective a := by
    intro z w hh
    have heq := A.injective hh
    exact Subtype.ext (congrArg (fun x : Disk => (x : V2)) heq)
  have har (z : Rim) : (a z : P2) ∈ r := (hAr _).mp z.property
  have hafull : range (fun z => (a z : P2)) = r := by
    apply Subset.antisymm
    · rintro _ ⟨z,rfl⟩; exact har z
    · intro x hx
      let y : d := ⟨x,hd.1 hx⟩
      have hy : (A.symm y : V2) ∈ Rim := (hAr _).mpr (by
        rw [A.apply_symm_apply]; exact hx)
      refine ⟨⟨A.symm y,hy⟩,?_⟩
      exact congrArg Subtype.val (A.apply_symm_apply y)
  let T : C(I × Rim,↥(S ∩ R)) := ⟨fun z =>
    ⟨H (z.1,a z.2),(hHmark z.1 (a z.2)).mpr (har z.2),(H (z.1,a z.2)).property⟩,
    (continuous_subtype_val.comp (H.continuous.comp
      (continuous_fst.prodMk (a.continuous.comp continuous_snd)))).subtype_mk _⟩
  let gamma : C(Rim,↥(S ∩ R)) := ⟨fun z => T (0,z),
    T.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let delta : C(Rim,↥(S ∩ R)) := ⟨fun z => T (1,z),
    T.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hzero (z : Rim) : (gamma z : X)=q (a z) := hH0 (a z)
  have hone (z : Rim) : (delta z : X)=k (a z) := hH1 (a z)
  refine ⟨gamma,delta,?_,?_,?_,?_,?_⟩
  · intro z w hh
    apply hai
    apply Subtype.ext
    exact hqi (a z).property (a w).property
      ((hzero z).symm.trans ((congrArg Subtype.val hh).trans (hzero w)))
  · intro z w hh
    apply hai
    apply Subtype.ext
    exact hki (a z).property (a w).property
      ((hone z).symm.trans ((congrArg Subtype.val hh).trans (hone w)))
  · apply Subset.antisymm
    · rintro _ ⟨z,rfl⟩; exact ⟨a z,har z,(hzero z).symm⟩
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨z,hz⟩ := hafull.symm.subset hx
      exact ⟨z,(hzero z).trans (congrArg q hz)⟩
  · apply Subset.antisymm
    · rintro _ ⟨z,rfl⟩; exact ⟨a z,har z,(hone z).symm⟩
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨z,hz⟩ := hafull.symm.subset hx
      exact ⟨z,(hone z).trans (congrArg k hz)⟩
  · exact ⟨{
      toContinuousMap := T
      map_zero_left := fun _ => rfl
      map_one_left := fun _ => rfl }⟩

end PoincareConjecture.M76

