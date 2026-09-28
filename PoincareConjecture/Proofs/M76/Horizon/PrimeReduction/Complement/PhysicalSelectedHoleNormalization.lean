import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.SelectedHoleDiskPortSourceUnion









set_option autoImplicit false

open Set Geometry Geometry.CubicalThreeSphere

namespace Set

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "P3" => (P2 × ℝ)

open PoincareConjecture.M76.HamiltonIndexTwoStandard



theorem exists_physical_selected_hole_normalization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Bool → Type*}
    (R : Bool → Set E) (a r : ∀ b, ι b → Set V4)
    (ha : ∀ b j, IsFinitePLBallPair V3 (a b j) (r b j))
    (haS : ∀ b j, a b j ⊆ sphere)
    (hopen : ∀ b j, IsOpen ((Subtype.val : sphere → V4) ⁻¹' (a b j \ r b j)))
    (hdis : ∀ b, Pairwise fun j k => Disjoint (a b j) (a b k)) (i : ∀ b, ι b)
    (C : ∀ b, R b ≃ₜ (sphere \ ⋃ j, a b j \ r b j : Set V4))
    (hC : ∀ b, (C b).IsFinitePL)
    {d q : Set E} (hd : IsFinitePLBallPair P2 d q)
    (hcontact : R false ∩ R true = d)
    (hport : ∀ b (x : R b), (x : E) ∈ d → (C b x : V4) ∈ r b (i b))
    (hout : ∀ b, ∃ x : R b, (C b x : V4) ∈ r b (i b) ∧ (x : E) ∉ d) :
    let B := fun b => sphere \ (a b (i b) \ r b (i b))
    let P := fun b : Bool => if b then prism 0 1 else prism (-1) 0
    let S := fun b : Bool => if b then (band 0 1 ∪ endDisk 0) ∪ endDisk 1
      else (band (-1) 0 ∪ endDisk (-1)) ∪ endDisk 0
    ∃ (f : Bool → E → V4) (n : Bool → V4 → P3) (N : ∀ b, B b ≃ₜ P b),
      (∀ b, FinitePiecewiseAffineOn (f b) (R b) ∧ InjOn (f b) (R b) ∧
        ∀ x : R b, (C b x : V4) = f b x) ∧
      (∀ b, (N b).IsFinitePL ∧ FinitePiecewiseAffineOn (n b) (B b) ∧
        InjOn (n b) (B b) ∧ (∀ x : B b, (N b x : P3) = n b x) ∧
        ∀ x : B b, (x : V4) ∈ r b (i b) ↔ (N b x : P3) ∈ S b) ∧
      EqOn (n false ∘ f false) (n true ∘ f true) d ∧
      (∀ b (x : R b), (x : E) ∈ d ↔ n b (f b x) ∈ endDisk 0) ∧
      ∀ b (x : R b), (x : E) ∈ q ↔ n b (f b x) ∈ endRim 0 := by
  dsimp only
  classical
  let B := fun b => sphere \ (a b (i b) \ r b (i b))
  let P := fun b : Bool => if b then prism 0 1 else prism (-1) 0
  let S := fun b : Bool => if b then (band 0 1 ∪ endDisk 0) ∪ endDisk 1
    else (band (-1) 0 ∪ endDisk (-1)) ∪ endDisk 0
  have hCambient (b : Bool) : ∃ f : E → V4,
      FinitePiecewiseAffineOn f (R b) ∧ InjOn f (R b) ∧
      ∀ x : R b, (C b x : V4) = f x := by
    obtain ⟨f,hf,hval⟩ := hC b
    refine ⟨f,hf,?_,hval⟩
    intro x hx y hy hxy
    exact congrArg Subtype.val ((C b).injective
      (Subtype.ext ((hval ⟨x,hx⟩).trans (hxy.trans (hval ⟨y,hy⟩).symm))))
  choose f hf hfi hval using hCambient
  have hdR (b : Bool) : d ⊆ R b := by
    cases b
    · exact fun _ hx => (hcontact.symm.subset hx).1
    · exact fun _ hx => (hcontact.symm.subset hx).2
  let D := fun b => f b '' d
  let Q := fun b => f b '' q
  have hD (b : Bool) : IsFinitePLBallPair P2 (D b) (Q b) :=
    hd.image_of_subset (hf b) (hdR b) (hfi b)
  have hDp (b : Bool) : D b ⊆ sphere \ ⋃ j, a b j \ r b j := by
    rintro _ ⟨x,hx,rfl⟩
    exact hval b ⟨x,hdR b hx⟩ ▸ (C b ⟨x,hdR b hx⟩).property
  have hDmark (b : Bool) (x : R b) : (x : E) ∈ d ↔ (C b x : V4) ∈ D b := by
    rw [hval]
    constructor
    · exact fun hx => ⟨x,hx,rfl⟩
    · rintro ⟨y,hy,hyx⟩
      exact hfi b (hdR b hy) x.property hyx ▸ hy
  let ed (b : Bool) := (C b).restrictSubsets (hdR b) (hDp b) (hDmark b)
  have hdcopy := hd
  obtain ⟨_,_,_,_,_,_,⟨_,⟨Kd,hKd,hKdd,_⟩,_⟩,_⟩ := hdcopy
  have hed (b : Bool) : (ed b).IsFinitePL :=
    (hC b).restrictSubsets (hdR b) (hDp b) (hDmark b) Kd hKd hKdd
  have hedval (b : Bool) (x : d) : (ed b x : V4) = f b x := hval b ⟨x,hdR b x.property⟩
  have hedq (b : Bool) (x : d) : (x : E) ∈ q ↔ (ed b x : V4) ∈ Q b := by
    rw [hedval]
    constructor
    · exact fun hx => ⟨x,hx,rfl⟩
    · rintro ⟨y,hy,hyx⟩
      exact hfi b (hdR b (hd.1 hy)) (hdR b x.property) hyx ▸ hy
  have hDr (b : Bool) : D b ⊆ r b (i b) := by
    rintro _ ⟨x,hx,rfl⟩
    exact hval b ⟨x,hdR b hx⟩ ▸ hport b ⟨x,hdR b hx⟩ hx
  have hDout (b : Bool) : (r b (i b) \ D b).Nonempty := by
    obtain ⟨x,hxr,hxd⟩ := hout b
    exact ⟨C b x,hxr,fun hx => hxd ((hDmark b x).mpr hx)⟩
  have hB (b : Bool) := selected_hole_punctured_ball
    (a b) (r b) (ha b) (haS b) (hopen b) (hdis b) (i b)
  obtain ⟨n₀,N₀,hN₀,hn₀,hni₀,hnval₀,hS₀,hd₀,_,_,_,_,hq₀⟩ :=
    exists_selected_hole_disk_port_normalization (a false) (r false) (ha false)
      (haS false) (hopen false) (hdis false) (i false) (hD false) (hDr false) (hDout false)
  have hD₀B := (hDr false).trans (hB false).1.1
  have hdP₀ : endDisk 0 ⊆ prism (-1) 0 :=
    subset_union_right.trans (prism_ballPair (by norm_num : (-1 : ℝ) < 0)).1
  let e₀ := N₀.restrictSubsets hD₀B hdP₀ hd₀
  have hDcopy := hD false
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K₀,hK₀,hK₀D,_⟩,_⟩,_⟩ := hDcopy
  have he₀ : e₀.IsFinitePL := hN₀.restrictSubsets hD₀B hdP₀ hd₀ K₀ hK₀ hK₀D
  let e₁ := (ed true).symm.trans ((ed false).trans e₀)
  have he₁ : e₁.IsFinitePL := (hed true).symm.trans ((hed false).trans he₀)
  have he₁q (x : D true) : (x : V4) ∈ Q true ↔ (e₁ x : P3) ∈ endRim 0 := by
    have hq := (hedq true ((ed true).symm x)).symm
    rw [(ed true).apply_symm_apply] at hq
    exact hq.trans ((hedq false ((ed true).symm x)).trans
      (hq₀ ⟨ed false ((ed true).symm x),hD₀B (ed false ((ed true).symm x)).property⟩))
  have hT := prism_ballPair (by norm_num : (0 : ℝ) < 1)
  have hdP₁ : endDisk 0 ⊆ (band 0 1 ∪ endDisk 0) ∪ endDisk 1 :=
    subset_union_right.trans subset_union_left
  have hOut : (((band 0 1 ∪ endDisk 0) ∪ endDisk 1) \ endDisk 0).Nonempty := by
    refine ⟨((0,0),1),Or.inr ?_,?_⟩
    · norm_num [endDisk,CoordinateHalfBoxes.base]
    · intro hx
      have hh : (1 : ℝ) = 0 := hx.2
      norm_num at hh
  obtain ⟨N₁,hN₁,hkeep₁,hS₁,hd₁⟩ := extend_actual_disk_port (hB true).1 hT
    (by simp) (by simp [Module.finrank_prod]) (hD true) (endDisk_ballPair 0)
    (hDr true) hdP₁ (hDout true) hOut e₁ he₁ he₁q
  have hN₁copy := hN₁
  obtain ⟨n₁,hn₁,hnval₁⟩ := hN₁copy
  have hni₁ : InjOn n₁ (B true) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (N₁.injective
      (Subtype.ext ((hnval₁ ⟨x,hx⟩).trans (hxy.trans (hnval₁ ⟨y,hy⟩).symm))))
  let n := fun b : Bool => if b then n₁ else n₀
  let N : ∀ b, B b ≃ₜ P b := fun b => by cases b; exact N₀; exact N₁
  have hnorm (b : Bool) :
      (N b).IsFinitePL ∧ FinitePiecewiseAffineOn (n b) (B b) ∧
      InjOn (n b) (B b) ∧ (∀ x : B b, (N b x : P3) = n b x) ∧
      ∀ x : B b, (x : V4) ∈ r b (i b) ↔ (N b x : P3) ∈ S b := by
    cases b
    · exact ⟨hN₀,hn₀,hni₀,hnval₀,hS₀⟩
    · exact ⟨hN₁,hn₁,hni₁,hnval₁,hS₁⟩
  have hnport (b : Bool) (x : B b) : (x : V4) ∈ D b ↔ (N b x : P3) ∈ endDisk 0 := by
    cases b
    · exact hd₀ x
    · exact hd₁ x
  have hphysicalPort (b : Bool) (x : R b) :
      (x : E) ∈ d ↔ n b (f b x) ∈ endDisk 0 := by
    have hCxB : (C b x : V4) ∈ B b :=
      ⟨(C b x).property.1,fun hh => (C b x).property.2 (mem_iUnion.mpr ⟨i b,hh⟩)⟩
    have hh := (hDmark b x).trans (hnport b ⟨C b x,hCxB⟩)
    rwa [(hnorm b).2.2.2.1,hval] at hh
  have hphysicalRim (b : Bool) (x : d) :
      (x : E) ∈ q ↔ n b (f b x) ∈ endRim 0 := by
    cases b
    · have hh := (hedq false x).trans
        (hq₀ ⟨ed false x,hD₀B (ed false x).property⟩)
      simpa only [hnval₀,hedval,n,Bool.false_eq_true,if_false] using hh
    · have hh := (hedq true x).trans (he₁q (ed true x))
      have hp := hkeep₁ (ed true x)
      have hv := hnval₁ ⟨ed true x,(hB true).1.1 (hDr true (ed true x).property)⟩
      rw [← hp,hv,hedval] at hh
      simpa only [n,if_true] using hh
  refine ⟨f,n,N,(fun b => ⟨hf b,hfi b,hval b⟩),hnorm,?_,hphysicalPort,?_⟩
  · intro x hx
    have hp := hkeep₁ (ed true ⟨x,hx⟩)
    have heq : e₁ (ed true ⟨x,hx⟩) = e₀ (ed false ⟨x,hx⟩) := by
      simp only [e₁,Homeomorph.trans_apply,Homeomorph.symm_apply_apply]
    rw [heq] at hp
    have hn0 := hnval₀ ⟨ed false ⟨x,hx⟩,hD₀B (ed false ⟨x,hx⟩).property⟩
    have hn1 := hnval₁ ⟨ed true ⟨x,hx⟩,(hB true).1.1 (hDr true (ed true ⟨x,hx⟩).property)⟩
    have hh := hn0.symm.trans (hp.symm.trans hn1)
    simpa only [hedval,Function.comp_apply,n,Bool.false_eq_true,if_false,if_true] using hh
  · intro b x
    constructor
    · intro hx
      exact (hphysicalRim b ⟨x,hd.1 hx⟩).mp hx
    · intro hx
      have hxd := (hphysicalPort b x).mpr ((endDisk_ballPair 0).1 hx)
      exact (hphysicalRim b ⟨x,hxd⟩).mpr hx

end Set
