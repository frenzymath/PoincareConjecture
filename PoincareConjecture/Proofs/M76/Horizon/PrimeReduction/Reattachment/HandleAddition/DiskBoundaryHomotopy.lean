import PoincareConjecture.Proofs.M76.Mathlib.ContractibleBallExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Push.FiniteDisk



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem exists_disk_extension_of_boundary_homotopy
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace Y]
    {D q : Set E} (hD : IsFinitePLBallPair P2 D q)
    (f g : C(q,Y)) (h : f.Homotopic g)
    (G : C(D,Y)) (hG : ∀ x : q, G ⟨x,hD.1 x.property⟩ = g x) :
    ∃ F : C(D,Y), ∀ x : q, F ⟨x,hD.1 x.property⟩ = f x := by
  have hstd : IsFinitePLBallPair P2 D2 Q2 :=
    (isFinitePLBallPair_unit_cube (ι := Fin 2)).model_equiv
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
  obtain ⟨H,_,hH⟩ := hstd.exists_homeomorph hD
  let b : C(Q2,q) := ⟨fun x => ⟨H ⟨x,sphere_subset_closedBall x.property⟩,
    (hH _).mp x.property⟩,by fun_prop⟩
  let inc : C(Q2,D2) := ⟨fun x => ⟨x,sphere_subset_closedBall x.property⟩,by fun_prop⟩
  let disk : C(D2,Y) := G.comp ⟨H,H.continuous⟩
  have hdisk : disk.Nullhomotopic := by
    let : ContractibleSpace D2 := (convex_closedBall (0 : V2) 1).contractibleSpace
      ⟨0,mem_closedBall_self (by norm_num)⟩
    simpa only [ContinuousMap.comp_id] using (id_nullhomotopic D2).comp_right disk
  have hb : disk.comp inc = g.comp b := by
    ext x
    exact hG (b x)
  obtain ⟨y,hy⟩ := hdisk.comp_left inc
  rw [hb] at hy
  have hn : (f.comp b).Nullhomotopic := ⟨y,(h.comp (ContinuousMap.Homotopic.refl b)).trans hy⟩
  obtain ⟨F,hF⟩ := hn.exists_closedBall_extension (f.comp b)
  refine ⟨F.comp ⟨H.symm,H.symm.continuous⟩,?_⟩
  intro x
  let z : Q2 := ⟨H.symm ⟨x,hD.1 x.property⟩,(hH _).mpr (by simp only [H.apply_symm_apply]; exact x.property)⟩
  have hz : (⟨z,sphere_subset_closedBall z.property⟩ : D2) =
      H.symm ⟨x,hD.1 x.property⟩ := rfl
  change F (H.symm ⟨x,hD.1 x.property⟩) = f x
  rw [←hz,hF]
  change f ⟨H (H.symm ⟨x,hD.1 x.property⟩), _⟩ = f x
  congr 1
  apply Subtype.ext
  change (H (H.symm ⟨x,hD.1 x.property⟩) : E) = (x : E)
  exact congrArg Subtype.val (H.apply_symm_apply ⟨x,hD.1 x.property⟩)

theorem no_disk_extension_of_boundary_homotopy
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace Y]
    {D q : Set E} (hD : IsFinitePLBallPair P2 D q)
    (f g : C(q,Y)) (h : f.Homotopic g)
    (hf : ¬ ∃ F : C(D,Y), ∀ x : q, F ⟨x,hD.1 x.property⟩ = f x) :
    ¬ ∃ G : C(D,Y), ∀ x : q, G ⟨x,hD.1 x.property⟩ = g x := by
  rintro ⟨G,hG⟩
  exact hf (exists_disk_extension_of_boundary_homotopy hD f g h G hG)

theorem no_frontier_extension_of_marked_disk_homotopy
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {D q : Set E} (hD : IsFinitePLBallPair (ℝ × ℝ) D q)
    {R : Set X} {f k : E → X}
    (hf : ContinuousOn f D) (hk : ContinuousOn k D)
    (hproper : ∀ x ∈ q, f x ∈ frontier R)
    (H : C(↥(Icc (0 : ℝ) 1) × ↥D,X))
    (hzero : ∀ x : D, H (⟨0,by norm_num⟩,x) = f x)
    (hone : ∀ x : D, H (⟨1,by norm_num⟩,x) = k x)
    (hfront : ∀ z, H z ∈ frontier R ↔ f z.2 ∈ frontier R)
    (hne : ¬ ∃ F : C(D,frontier R),
      ∀ x : q, (F ⟨x,hD.1 x.property⟩ : X) = f x) :
    ¬ ∃ G : C(D,frontier R),
      ∀ x : q, (G ⟨x,hD.1 x.property⟩ : X) = k x := by
  have hkfront (x : q) : k x ∈ frontier R := by
    rw [←hone ⟨x,hD.1 x.property⟩]
    exact (hfront _).mpr (hproper x x.property)
  let fR : C(q,frontier R) := ⟨fun x => ⟨f x,hproper x x.property⟩,
    (hf.mono hD.1).domRestrict.subtype_mk _⟩
  let kR : C(q,frontier R) := ⟨fun x => ⟨k x,hkfront x⟩,
    (hk.mono hD.1).domRestrict.subtype_mk _⟩
  let h : fR.Homotopy kR := {
    toFun := fun z => ⟨H (z.1,⟨z.2,hD.1 z.2.property⟩),
      (hfront _).mpr (hproper z.2 z.2.property)⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact H.continuous.comp (continuous_fst.prodMk
        ((continuous_subtype_val.comp continuous_snd).subtype_mk _))
    map_zero_left := fun x => Subtype.ext (hzero ⟨x,hD.1 x.property⟩)
    map_one_left := fun x => Subtype.ext (hone ⟨x,hD.1 x.property⟩) }
  have hn : ¬ ∃ F : C(D,frontier R), ∀ x : q,F ⟨x,hD.1 x.property⟩ = fR x := by
    rintro ⟨F,hF⟩
    exact hne ⟨F,fun x => congrArg Subtype.val (hF x)⟩
  rintro ⟨G,hG⟩
  exact no_disk_extension_of_boundary_homotopy hD fR kR ⟨h⟩ hn
    ⟨G,fun x => Subtype.ext (hG x)⟩

theorem exists_pasted_relative_disk_homotopy
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {D N C W : Set E} (hN : IsClosed N) (hC : IsClosed C)
    (hcover : D ⊆ N ∪ C) (hseam : N ∩ C = W)
    {f g k : E → X} (hf : ContinuousOn f D)
    (hkN : EqOn k g N) (hkC : EqOn k f (D ∩ C))
    (H : C(↥(Icc (0 : ℝ) 1) × ↥N,X))
    (hzero : ∀ x : N,H (⟨0,by norm_num⟩,x) = f x)
    (hone : ∀ x : N,H (⟨1,by norm_num⟩,x) = g x)
    (hfix : ∀ z,(z.2 : E) ∈ W → H z = f z.2)
    {R : Set X} (hfR : MapsTo f D R) (hHR : ∀ z,H z ∈ R)
    (hfront : ∀ z,H z ∈ frontier R ↔ f z.2 ∈ frontier R) :
    ∃ G : C(↥(Icc (0 : ℝ) 1) × ↥D,X),
      (∀ x : D,G (⟨0,by norm_num⟩,x) = f x) ∧
      (∀ x : D,G (⟨1,by norm_num⟩,x) = k x) ∧
      (∀ z,G z ∈ R) ∧
      (∀ z,G z ∈ frontier R ↔ f z.2 ∈ frontier R) ∧
      ∀ z,(z.2 : E) ∈ C → G z = f z.2 := by
  classical
  let I := Icc (0 : ℝ) 1
  let A : Set (I × D) := {z | (z.2 : E) ∈ N}
  let B : Set (I × D) := {z | (z.2 : E) ∈ C}
  let v : I × D → X := fun z => if hz : (z.2 : E) ∈ N then H (z.1,⟨z.2,hz⟩) else f z.2
  have hvA (z : I × D) (hz : z ∈ A) : v z = H (z.1,⟨z.2,hz⟩) := by
    change (z.2 : E) ∈ N at hz
    simp only [v,dif_pos hz]
  have hvB (z : I × D) (hz : z ∈ B) : v z = f z.2 := by
    dsimp only [v]
    split_ifs with hn
    · exact hfix _ (hseam.subset ⟨hn,hz⟩)
    · rfl
  have hcA : ContinuousOn v A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun z : A => H (z.val.1,⟨z.val.2,z.property⟩)) := by
      apply H.continuous.comp
      fun_prop
    exact hc.congr (fun z => (hvA z z.property).symm)
  have hcB : ContinuousOn v B := by
    have hc : Continuous (fun z : I × D => f z.2) :=
      hf.domRestrict.comp continuous_snd
    exact hc.continuousOn.congr (fun z hz => hvB z hz)
  have hAB : A ∪ B = univ := by
    ext z
    simp only [mem_union,mem_univ,iff_true]
    exact hcover z.2.property
  have hvc : Continuous v := by
    have hc := hcA.union_of_isClosed hcB
      (hN.preimage (continuous_subtype_val.comp continuous_snd))
      (hC.preimage (continuous_subtype_val.comp continuous_snd))
    rw [hAB] at hc
    exact continuousOn_univ.mp hc
  refine ⟨⟨v,hvc⟩,?_,?_,?_,?_,?_⟩
  · intro x
    change v (⟨0,by norm_num [I]⟩,x) = f x
    by_cases hx : (x : E) ∈ N
    · rw [hvA _ hx]; exact hzero ⟨x,hx⟩
    · simp only [v,dif_neg hx]
  · intro x
    change v (⟨1,by norm_num [I]⟩,x) = k x
    by_cases hx : (x : E) ∈ N
    · rw [hvA _ hx]; exact (hone ⟨x,hx⟩).trans (hkN hx).symm
    · rw [hvB _ ((hcover x.property).resolve_left hx)]
      exact (hkC ⟨x.property,(hcover x.property).resolve_left hx⟩).symm
  · intro z
    change v z ∈ R
    by_cases hz : (z.2 : E) ∈ N
    · rw [hvA _ hz]; exact hHR _
    · rw [hvB _ ((hcover z.2.property).resolve_left hz)]
      exact hfR z.2.property
  · intro z
    change v z ∈ frontier R ↔ f z.2 ∈ frontier R
    by_cases hz : (z.2 : E) ∈ N
    · rw [hvA _ hz]; exact hfront _
    · rw [hvB _ ((hcover z.2.property).resolve_left hz)]
  · exact hvB

end PoincareConjecture.M76
