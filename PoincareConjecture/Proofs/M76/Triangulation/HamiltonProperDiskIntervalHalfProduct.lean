import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalEndpointExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalPrismRim











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem exists_vertical_image_chart {α β : ℝ} (hαβ : α < β)
    (a : E) (f : ℝ → E) (hf : FinitePiecewiseAffineOn f (Icc α β))
    (hi : InjOn f (Icc α β)) :
    IsFinitePLBallPair ℝ ({a} ×ˢ Icc α β : Set (E × ℝ)) {(a, α), (a, β)} ∧
      ∃ e : ({a} ×ˢ Icc α β : Set (E × ℝ)) ≃ₜ (f '' Icc α β),
        e.IsFinitePL ∧ ∀ x, (e x : E) = f (x : E × ℝ).2 := by
  have hI := isFinitePLBallPair_Icc hαβ
  have hcopy := hI
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ := hcopy
  let j : ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.const ℝ ℝ a).prod (ContinuousAffineMap.id ℝ ℝ)
  have hj : FinitePiecewiseAffineOn j (Icc α β) :=
    ⟨K, hK, hKI, K.affineOnFaces_affine j⟩
  have hji : InjOn j (Icc α β) := fun _ _ _ _ h => congrArg Prod.snd h
  have hjimage : j '' Icc α β = ({a} ×ˢ Icc α β : Set (E × ℝ)) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨rfl, ht⟩
    · rintro ⟨hx, ht⟩
      exact ⟨x.2, ht, Prod.ext hx.symm rfl⟩
  have hpair := hI.affine_image j hji
  have hpair' : IsFinitePLBallPair ℝ ({a} ×ˢ Icc α β : Set (E × ℝ))
      {(a, α), (a, β)} := by
    rw [hjimage, image_pair] at hpair
    simpa only [j, ContinuousAffineMap.prod_apply, ContinuousAffineMap.coe_const,
      ContinuousAffineMap.coe_id, Function.const_apply, id_eq] using hpair
  have hex := hj.exists_homeomorph_image hji
  rw [hjimage] at hex
  obtain ⟨J, hJ, hJval⟩ := hex
  obtain ⟨F, hF, hFval⟩ := hf.exists_homeomorph_image hi
  refine ⟨hpair', J.symm.trans F, hJ.symm.trans hF, ?_⟩
  intro x
  have hx : J ⟨(x : E × ℝ).2, x.property.2⟩ = x := by
    apply Subtype.ext
    rw [hJval]
    exact Prod.ext x.property.1.symm rfl
  change (F (J.symm x) : E) = f (x : E × ℝ).2
  have hinv : J.symm x = ⟨(x : E × ℝ).2, x.property.2⟩ := by
    exact (congrArg J.symm hx.symm).trans (J.symm_apply_apply _)
  rw [hinv, hFval]

private theorem exists_horizontal_identity {B : Set E} {a z : E}
    (hB : IsFinitePLBallPair ℝ B {a, z}) (α : ℝ) :
    ∃ e : (B ×ˢ {α} : Set (E × ℝ)) ≃ₜ B,
      e.IsFinitePL ∧ ∀ x, (e x : E) = (x : E × ℝ).1 := by
  have hcopy := hB
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKB, _⟩, _⟩, _⟩ := hcopy
  let j : E →ᴬ[ℝ] E × ℝ :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E α)
  have hj : FinitePiecewiseAffineOn j B := ⟨K, hK, hKB, K.affineOnFaces_affine j⟩
  have hji : InjOn j B := fun _ _ _ _ h => congrArg Prod.fst h
  have hjimage : j '' B = (B ×ˢ {α} : Set (E × ℝ)) := by
    change (fun x : E => (x, α)) '' B = B ×ˢ {α}
    exact (prod_singleton (s := B) (b := α)).symm
  have hex := hj.exists_homeomorph_image hji
  rw [hjimage] at hex
  obtain ⟨J, hJ, hJval⟩ := hex
  refine ⟨J.symm, hJ.symm, ?_⟩
  intro x
  have hx : J ⟨(x : E × ℝ).1, x.property.1⟩ = x := by
    apply Subtype.ext
    rw [hJval]
    exact Prod.ext rfl x.property.2.symm
  have hinv : J.symm x = ⟨(x : E × ℝ).1, x.property.1⟩ := by
    exact (congrArg J.symm hx.symm).trans (J.symm_apply_apply _)
  exact congrArg Subtype.val hinv





theorem exists_interval_half_product {B N Q : Set E} (a : Bool → E)
    (hB : IsFinitePLBallPair ℝ B {a false, a true}) (ha : a false ≠ a true)
    (hN : IsFinitePLBallPair (ℝ × ℝ) N (B ∪ Q))
    (hQ : IsFinitePLBallPair ℝ Q {a false, a true})
    (hBQ : B ∩ Q = {a false, a true}) {α β : ℝ} (hαβ : α < β)
    (F : Bool → ℝ → E)
    (hF : ∀ i, FinitePiecewiseAffineOn (F i) (Icc α β))
    (hi : ∀ i, InjOn (F i) (Icc α β))
    (hFa : ∀ i, F i α = a i)
    (hFQ : ∀ i, F i '' Icc α β ⊆ Q)
    (hdis : Disjoint (F false '' Icc α β) (F true '' Icc α β)) :
    ∃ H : (B ×ˢ Icc α β : Set (E × ℝ)) ≃ₜ N, H.IsFinitePL ∧
      (∀ x : B, (H ⟨((x : E), α), x.property, le_rfl, hαβ.le⟩ : E) = x) ∧
      (∀ i (t : Icc α β),
        (H ⟨(a i, (t : ℝ)), by
          refine ⟨hB.1 ?_, t.property⟩
          cases i <;> simp⟩ : E) = F i t) ∧
      (∀ x : (B ×ˢ Icc α β : Set (E × ℝ)),
        (H x : E) ∈ Q ↔ (x : E × ℝ).1 ∈ ({a false, a true} : Set E) ∨
          (x : E × ℝ).2 = β) ∧
      ∀ x : (B ×ˢ Icc α β : Set (E × ℝ)),
        (H x : E) ∈ B ↔ (x : E × ℝ).2 = α := by
  have hI := isFinitePLBallPair_Icc hαβ
  let A : Set (E × ℝ) := B ×ˢ {α}
  let U : Set (E × ℝ) := ({a false, a true} ×ˢ Icc α β) ∪ (B ×ˢ {β})
  let d : Bool → Set (E × ℝ) := fun i => {a i} ×ˢ Icc α β
  let D : Bool → Set E := fun i => F i '' Icc α β
  let aS : Bool → E × ℝ := fun i => (a i, α)
  let cS : Bool → E × ℝ := fun i => (a i, β)
  let C : Bool → E := fun i => F i β
  have harcs := hB.interval_prism_rim_arcs ha hαβ false
  change IsFinitePLBallPair ℝ A {aS false, aS true} ∧
    IsFinitePLBallPair ℝ U {aS false, aS true} ∧
    A ∪ U = ({a false, a true} ×ˢ Icc α β) ∪ (B ×ˢ {α, β}) ∧
    A ∩ U = {aS false, aS true} at harcs
  have hdi (i : Bool) :
      IsFinitePLBallPair ℝ (d i) {aS i, cS i} ∧
        ∃ e : d i ≃ₜ D i, e.IsFinitePL ∧
          ∀ x, (e x : E) = F i (x : E × ℝ).2 :=
    exists_vertical_image_chart hαβ (a i) (F i) (hF i) (hi i)
  choose e he heval using fun i => (hdi i).2
  have hDi (i : Bool) : IsFinitePLBallPair ℝ (D i) {a i, C i} := by
    simpa only [D, C, image_pair, hFa i] using hI.image (hF i) (hi i)
  have hds (i : Bool) : d i ⊆ U := by
    intro x hx
    refine Or.inl ⟨?_, hx.2⟩
    cases i
    · exact Or.inl hx.1
    · exact Or.inr hx.1
  have hsourceDis : Disjoint (d false) (d true) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact ha (hx.1.symm.trans hy.1)
  have hAC (i : Bool) : a i ≠ C i := by
    intro h
    exact hαβ.ne (hi i ⟨le_rfl, hαβ.le⟩ ⟨hαβ.le, le_rfl⟩ ((hFa i).trans h))
  obtain ⟨u, hu, hukeep, _, hua⟩ :=
    IsFinitePLBallPair.exists_extension_of_disjoint_end_intervals
      d D aS cS a C harcs.2.1 hQ (fun i => (hdi i).1) hDi hds hFQ
      (fun h => ha (congrArg Prod.fst h)) ha
      (fun _ h => hαβ.ne (congrArg Prod.snd h)) hAC hsourceDis hdis e he
      (fun i => (heval i _).trans (hFa i)) (fun i => heval i _)
  obtain ⟨z, hz, hzval⟩ := exists_horizontal_identity hB α
  have hAz (x : A) : (x : E × ℝ) ∈ U ↔ (z x : E) ∈ Q := by
    have hsource : (x : E × ℝ) ∈ U ↔
        (x : E × ℝ) ∈ ({aS false, aS true} : Set (E × ℝ)) := by
      rw [← harcs.2.2.2]
      simp only [mem_inter_iff, x.property, true_and]
    have htarget : (z x : E) ∈ Q ↔ (z x : E) ∈ ({a false, a true} : Set E) := by
      rw [← hBQ]
      simp only [mem_inter_iff, (z x).property, true_and]
    rw [hsource, htarget, hzval]
    have htime : (x : E × ℝ).2 = α := x.property.2
    simp only [aS, mem_insert_iff, mem_singleton_iff, Prod.ext_iff, htime, and_true]
  have hagree (x : E × ℝ) (hxA : x ∈ A) (hxU : x ∈ U) :
      (z ⟨x, hxA⟩ : E) = u ⟨x, hxU⟩ := by
    have hxends : x ∈ ({aS false, aS true} : Set (E × ℝ)) :=
      harcs.2.2.2.subset ⟨hxA, hxU⟩
    rw [hzval]
    rcases hxends with hx | hx
    · have h := hua false
      have heq : (⟨x, hxU⟩ : U) = ⟨aS false, hds false ((hdi false).1.1 (Or.inl rfl))⟩ :=
        Subtype.ext hx
      rw [heq, h]
      exact congrArg Prod.fst hx
    · have h := hua true
      have heq : (⟨x, hxU⟩ : U) = ⟨aS true, hds true ((hdi true).1.1 (Or.inl rfl))⟩ :=
        Subtype.ext hx
      rw [heq, h]
      exact congrArg Prod.fst hx
  obtain ⟨v, hv, hvA, hvU⟩ := Homeomorph.exists_union_finitePL z u hz hu hAz hagree
  have hrect : IsFinitePLBallPair (ℝ × ℝ) (B ×ˢ Icc α β) (A ∪ U) := by
    rw [harcs.2.2.1]
    exact hB.prod hI
  obtain ⟨H, hH, hHv, _⟩ := hrect.exists_extension hN v hv
  have hHA (x : A) : (H ⟨x, hrect.1 (Or.inl x.property)⟩ : E) = z x :=
    (congrArg Subtype.val (hHv ⟨x, Or.inl x.property⟩)).trans (hvA x)
  have hHU (x : U) : (H ⟨x, hrect.1 (Or.inr x.property)⟩ : E) = u x :=
    (congrArg Subtype.val (hHv ⟨x, Or.inr x.property⟩)).trans (hvU x)
  have hAmem := H.mem_subset_iff_of_extension z
    (fun _ hx => hrect.1 (Or.inl hx)) (fun _ hx => hN.1 (Or.inl hx))
    (fun x => Subtype.ext (hHA x))
  have hUmem := H.mem_subset_iff_of_extension u
    (fun _ hx => hrect.1 (Or.inr hx)) (fun _ hx => hN.1 (Or.inr hx))
    (fun x => Subtype.ext (hHU x))
  refine ⟨H, hH, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (hHA ⟨((x : E), α), x.property, rfl⟩).trans (hzval _)
  · intro i t
    have h := congrArg Subtype.val (hukeep i ⟨(a i, (t : ℝ)), rfl, t.property⟩)
    exact (hHU ⟨(a i, (t : ℝ)), hds i ⟨rfl, t.property⟩⟩).trans
      (h.trans (heval i _))
  · intro x
    rw [← hUmem x]
    change (((x : E × ℝ).1 ∈ {a false, a true} ∧ (x : E × ℝ).2 ∈ Icc α β) ∨
      ((x : E × ℝ).1 ∈ B ∧ (x : E × ℝ).2 = β)) ↔ _
    simp only [x.property.1, x.property.2, and_true, true_and]
  · intro x
    rw [← hAmem x]
    change ((x : E × ℝ).1 ∈ B ∧ (x : E × ℝ).2 = α) ↔ _
    simp only [x.property.1, true_and]

end PoincareConjecture.M76.HamiltonIndexOne
