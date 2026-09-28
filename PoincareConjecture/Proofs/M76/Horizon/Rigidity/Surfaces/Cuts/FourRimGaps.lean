import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalMiddle
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem prescribed_interval_coordinates
    {f : ℝ → E} (hf : FinitePiecewiseAffineOn f (Icc 0 1))
    (hi : InjOn f (Icc 0 1)) {B : Set E} {a b : E}
    (hB : IsFinitePLBallPair ℝ B {a, b}) (hab : a ≠ b)
    (hsub : B ⊆ f '' Icc 0 1) (h0 : f 0 ∉ B) (h1 : f 1 ∉ B) :
    ∃ l r : ℝ, 0 < l ∧ l < r ∧ r < 1 ∧
      B = f '' Icc l r ∧ ({f l, f r} : Set E) = {a, b} := by
  obtain ⟨u, hu, hfu⟩ := hsub (hB.1 (show a ∈ ({a,b} : Set E) by simp))
  obtain ⟨v, hv, hfv⟩ := hsub (hB.1 (show b ∈ ({a,b} : Set E) by simp))
  have huv : u ≠ v := fun h => hab (hfu.symm.trans (h ▸ hfv))
  have hu0 : 0 < u := by
    by_contra h
    have he : u = 0 := le_antisymm (le_of_not_gt h) hu.1
    exact h0 (he ▸ hfu.symm ▸ hB.1 (by simp))
  have hv0 : 0 < v := by
    by_contra h
    have he : v = 0 := le_antisymm (le_of_not_gt h) hv.1
    exact h0 (he ▸ hfv.symm ▸ hB.1 (by simp))
  have hu1 : u < 1 := by
    by_contra h
    have he : u = 1 := le_antisymm hu.2 (le_of_not_gt h)
    exact h1 (he ▸ hfu.symm ▸ hB.1 (by simp))
  have hv1 : v < 1 := by
    by_contra h
    have he : v = 1 := le_antisymm hv.2 (le_of_not_gt h)
    exact h1 (he ▸ hfv.symm ▸ hB.1 (by simp))
  rcases lt_or_gt_of_ne huv with huv | hvu
  · refine ⟨u, v, hu0, huv, hv1, ?_, by rw [hfu, hfv]⟩
    have hp : IsFinitePLBallPair ℝ B {f u,f v} := by rwa [hfu,hfv]
    exact hp.eq_image_Icc_of_subset hf hi huv
      (fun _ hx => ⟨hu.1.trans hx.1,hx.2.trans hv.2⟩) hsub
  · refine ⟨v, u, hv0, hvu, hu1, ?_, by rw [hfu,hfv,pair_comm]⟩
    have hp : IsFinitePLBallPair ℝ B {f v,f u} := by
      simpa only [hfu,hfv,pair_comm b a] using hB
    exact hp.eq_image_Icc_of_subset hf hi hvu
      (fun _ hx => ⟨hv.1.trans hx.1,hx.2.trans hu.2⟩) hsub

private theorem exists_ordering_of_injective (l : Fin 3 → ℝ)
    (hl : Function.Injective l) :
    ∃ σ : Fin 3 ≃ Fin 3, StrictMono (l ∘ σ) := by
  classical
  let S := Finset.univ.image l
  have hcard : S.card = 3 := by simp [S,Finset.card_image_of_injective _ hl]
  let e : Fin 3 ≃ S := Equiv.ofBijective
    (fun i => ⟨l i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun i j h => hl (congrArg Subtype.val h), by
      rintro ⟨y,hy⟩
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
      exact ⟨i,rfl⟩⟩
  let σ := (S.orderIsoOfFin hcard).toEquiv.trans e.symm
  refine ⟨σ, ?_⟩
  have heq : l ∘ σ = S.orderEmbOfFin hcard := by
    funext i
    exact congrArg Subtype.val (e.apply_symm_apply (S.orderIsoOfFin hcard i))
  rw [heq]
  exact (S.orderEmbOfFin hcard).strictMono

structure FourRimBridgeCoordinates (q : Set E) (B : Fin 4 → Set E)
    (a b : Fin 4 → E) where
  map : ℝ → E
  finitePL : FinitePiecewiseAffineOn map (Icc 0 1)
  injective : InjOn map (Icc 0 1)
  order : Fin 3 ≃ Fin 3
  lo : Fin 3 → ℝ
  hi : Fin 3 → ℝ
  positive : ∀ i, 0 < lo i
  nondegenerate : ∀ i, lo i < hi i
  bounded : ∀ i, hi i < 1
  separated : ∀ i j, i < j → hi i < lo j
  zero : map 0 = a 0
  one : map 1 = b 0
  cover : B 0 ∪ map '' Icc 0 1 = q
  contact : B 0 ∩ map '' Icc 0 1 = {map 0,map 1}
  bridge : ∀ i, B (order i).succ = map '' Icc (lo i) (hi i)
  endpoints : ∀ i, ({map (lo i),map (hi i)} : Set E) =
    {a (order i).succ,b (order i).succ}

theorem exists_four_rim_bridge_coordinates
    {d q : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (B : Fin 4 → Set E) (a b : Fin 4 → E)
    (hB : ∀ i, IsFinitePLBallPair ℝ (B i) {a i,b i})
    (hab : ∀ i, a i ≠ b i) (hsub : ∀ i, B i ⊆ q)
    (hdis : Pairwise (fun i j => Disjoint (B i) (B j))) :
    Nonempty (FourRimBridgeCoordinates q B a b) := by
  classical
  obtain ⟨V,hV,hcover,hcontact⟩ := hd.exists_boundary_arc_complement
    (hB 0) (hsub 0) (hab 0)
  obtain ⟨e,⟨f,hf,heval⟩,he0,he1⟩ :=
    hV.exists_unitInterval_chart_with_endpoints (hab 0)
  have hi : InjOn f (Icc 0 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext
      ((heval ⟨x,hx⟩).trans (hxy.trans (heval ⟨y,hy⟩).symm))))
  have hfs : f '' Icc 0 1 = V := by
    apply Subset.antisymm
    · rintro _ ⟨t,ht,rfl⟩
      exact heval ⟨t,ht⟩ ▸ (e ⟨t,ht⟩).property
    · intro x hx
      refine ⟨e.symm ⟨x,hx⟩,(e.symm ⟨x,hx⟩).property,?_⟩
      exact (heval _).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩))
  have hf0 : f 0 = a 0 := (heval ⟨0,by constructor <;> norm_num⟩).symm.trans he0
  have hf1 : f 1 = b 0 := (heval ⟨1,by constructor <;> norm_num⟩).symm.trans he1
  have hremaining (i : Fin 3) : B i.succ ⊆ f '' Icc 0 1 := by
    rw [hfs]
    intro x hx
    have hxq := hcover.symm.subset (hsub i.succ hx)
    exact hxq.resolve_left (fun h => disjoint_left.mp
      (hdis (Fin.succ_ne_zero i)) hx h)
  have hparams (i : Fin 3) : ∃ l r : ℝ, 0 < l ∧ l < r ∧ r < 1 ∧
      B i.succ = f '' Icc l r ∧ ({f l,f r} : Set E) = {a i.succ,b i.succ} := by
    apply prescribed_interval_coordinates hf hi (hB i.succ) (hab i.succ) (hremaining i)
    · intro hx
      exact disjoint_left.mp (hdis (Fin.succ_ne_zero i)) hx
        (hf0.symm ▸ (hB 0).1 (by simp))
    · intro hx
      exact disjoint_left.mp (hdis (Fin.succ_ne_zero i)) hx
        (hf1.symm ▸ (hB 0).1 (by simp))
  choose l r hl hlr hr hBr hend using hparams
  have hlinj : Function.Injective l := by
    intro i j he
    by_contra hij
    have hx : f (l i) ∈ B i.succ := hBr i ▸ ⟨l i,⟨le_rfl,(hlr i).le⟩,rfl⟩
    have hy : f (l j) ∈ B j.succ := hBr j ▸ ⟨l j,⟨le_rfl,(hlr j).le⟩,rfl⟩
    exact disjoint_left.mp (hdis (fun h => hij (Fin.succ_injective _ h))) hx (he ▸ hy)
  obtain ⟨σ,hσ⟩ := exists_ordering_of_injective l hlinj
  have hsep (i j : Fin 3) (hij : i < j) : r (σ i) < l (σ j) := by
    by_contra h
    have hlow : l (σ i) < l (σ j) := hσ hij
    have hx : f (l (σ j)) ∈ B (σ i).succ := hBr (σ i) ▸
      ⟨l (σ j),⟨hlow.le,le_of_not_gt h⟩,rfl⟩
    have hy : f (l (σ j)) ∈ B (σ j).succ := hBr (σ j) ▸
      ⟨l (σ j),⟨le_rfl,(hlr (σ j)).le⟩,rfl⟩
    exact disjoint_left.mp (hdis (fun he => hij.ne
      (σ.injective (Fin.succ_injective _ he)))) hx hy
  exact ⟨⟨f,hf,hi,σ,l ∘ σ,r ∘ σ,fun i => hl (σ i),fun i => hlr (σ i),
    fun i => hr (σ i),hsep,hf0,hf1,by rwa [hfs],by rwa [hfs,hf0,hf1],
    fun i => hBr (σ i),fun i => hend (σ i)⟩⟩

namespace FourRimBridgeCoordinates

variable {q : Set E} {B : Fin 4 → Set E} {a b : Fin 4 → E}

def gapLo (C : FourRimBridgeCoordinates q B a b) : Fin 4 → ℝ :=
  ![0,C.hi 0,C.hi 1,C.hi 2]

def gapHi (C : FourRimBridgeCoordinates q B a b) : Fin 4 → ℝ :=
  ![C.lo 0,C.lo 1,C.lo 2,1]

def gap (C : FourRimBridgeCoordinates q B a b) (i : Fin 4) : Set E :=
  C.map '' Icc (C.gapLo i) (C.gapHi i)

omit [FiniteDimensional ℝ E] in
theorem gap_parameter_bounds (C : FourRimBridgeCoordinates q B a b) (i : Fin 4) :
    0 ≤ C.gapLo i ∧ C.gapLo i < C.gapHi i ∧ C.gapHi i ≤ 1 := by
  have hp0 := C.positive 0
  have hp1 := C.positive 1
  have hp2 := C.positive 2
  have hn0 := C.nondegenerate 0
  have hn1 := C.nondegenerate 1
  have hn2 := C.nondegenerate 2
  have hb0 := C.bounded 0
  have hb1 := C.bounded 1
  have hb2 := C.bounded 2
  have hs01 := C.separated 0 1 (by decide)
  have hs12 := C.separated 1 2 (by decide)
  fin_cases i <;> dsimp [gapLo,gapHi] <;>
    constructor <;> first | (constructor <;> linarith) | linarith

omit [FiniteDimensional ℝ E] in
theorem gap_parameter_subset (C : FourRimBridgeCoordinates q B a b) (i : Fin 4) :
    Icc (C.gapLo i) (C.gapHi i) ⊆ Icc (0 : ℝ) 1 := by
  intro t ht
  have h := C.gap_parameter_bounds i
  exact ⟨h.1.trans ht.1,ht.2.trans h.2.2⟩

theorem gap_isFinitePLBallPair (C : FourRimBridgeCoordinates q B a b) (i : Fin 4) :
    IsFinitePLBallPair ℝ (C.gap i) {C.map (C.gapLo i),C.map (C.gapHi i)} := by
  simpa only [gap,image_pair] using
    (isFinitePLBallPair_Icc (C.gap_parameter_bounds i).2.1).image_of_subset
      C.finitePL (C.gap_parameter_subset i) C.injective

theorem gap_endpoints_ne (C : FourRimBridgeCoordinates q B a b) (i : Fin 4) :
    C.map (C.gapLo i) ≠ C.map (C.gapHi i) := by
  have h := C.gap_parameter_bounds i
  exact fun he => h.2.1.ne (C.injective
    (C.gap_parameter_subset i ⟨le_rfl,h.2.1.le⟩)
    (C.gap_parameter_subset i ⟨h.2.1.le,le_rfl⟩) he)

theorem gap_subset (C : FourRimBridgeCoordinates q B a b) (i : Fin 4) :
    C.gap i ⊆ q := by
  intro x hx
  exact C.cover.subset (Or.inr (image_mono (C.gap_parameter_subset i) hx))

theorem gaps_cover (C : FourRimBridgeCoordinates q B a b) :
    {x | (∃ i, x ∈ B i) ∨ ∃ i, x ∈ C.gap i} = q := by
  apply Subset.antisymm
  · rintro x (⟨i,hi⟩ | ⟨i,hi⟩)
    · cases i using Fin.cases with
      | zero => exact C.cover.subset (Or.inl hi)
      | succ i =>
        have hb := C.bridge (C.order.symm i)
        rw [C.order.apply_symm_apply] at hb
        obtain ⟨t,ht,rfl⟩ := hb ▸ hi
        exact C.cover.subset (Or.inr ⟨t,⟨(C.positive _).le.trans ht.1,
          ht.2.trans (C.bounded _).le⟩,rfl⟩)
    · exact C.gap_subset i hi
  · intro x hx
    rcases C.cover.symm.subset hx with h0 | ⟨t,ht,rfl⟩
    · exact Or.inl ⟨0,h0⟩
    by_cases h0 : t ≤ C.lo 0
    · exact Or.inr ⟨0,t,⟨ht.1,h0⟩,rfl⟩
    by_cases h1 : t ≤ C.hi 0
    · exact Or.inl ⟨(C.order 0).succ,(C.bridge 0).symm ▸
        ⟨t,⟨(le_of_not_ge h0),h1⟩,rfl⟩⟩
    by_cases h2 : t ≤ C.lo 1
    · exact Or.inr ⟨1,t,⟨le_of_not_ge h1,h2⟩,rfl⟩
    by_cases h3 : t ≤ C.hi 1
    · exact Or.inl ⟨(C.order 1).succ,(C.bridge 1).symm ▸
        ⟨t,⟨le_of_not_ge h2,h3⟩,rfl⟩⟩
    by_cases h4 : t ≤ C.lo 2
    · exact Or.inr ⟨2,t,⟨le_of_not_ge h3,h4⟩,rfl⟩
    by_cases h5 : t ≤ C.hi 2
    · exact Or.inl ⟨(C.order 2).succ,(C.bridge 2).symm ▸
        ⟨t,⟨le_of_not_ge h4,h5⟩,rfl⟩⟩
    · exact Or.inr ⟨3,t,⟨le_of_not_ge h5,ht.2⟩,rfl⟩

theorem gaps_pairwise_disjoint (C : FourRimBridgeCoordinates q B a b) :
    Pairwise (fun i j => Disjoint (C.gap i) (C.gap j)) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro x ⟨s,hs,hsx⟩ ⟨t,ht,htx⟩
  have heq := C.injective (C.gap_parameter_subset i hs)
    (C.gap_parameter_subset j ht) (hsx.trans htx.symm)
  subst t
  have hn0 := C.nondegenerate 0
  have hn1 := C.nondegenerate 1
  have hn2 := C.nondegenerate 2
  have hs01 := C.separated 0 1 (by decide)
  have hs12 := C.separated 1 2 (by decide)
  fin_cases i <;> fin_cases j <;>
    dsimp [gapLo,gapHi] at hs ht <;>
    first | exact (hij rfl).elim | linarith [hs.1,hs.2,ht.1,ht.2]

omit [FiniteDimensional ℝ E] in
private theorem gap_parameter_contact (C : FourRimBridgeCoordinates q B a b)
    (i : Fin 4) (j : Fin 3) (t : ℝ) :
    (t ∈ Icc (C.gapLo i) (C.gapHi i) ∧ t ∈ Icc (C.lo j) (C.hi j)) ↔
      (i.val = j.val ∧ t = C.lo j) ∨ (i.val = j.val + 1 ∧ t = C.hi j) := by
  have hp0 := C.positive 0
  have hn0 := C.nondegenerate 0
  have hn1 := C.nondegenerate 1
  have hn2 := C.nondegenerate 2
  have hb2 := C.bounded 2
  have hs01 := C.separated 0 1 (by decide)
  have hs12 := C.separated 1 2 (by decide)
  fin_cases i <;> fin_cases j <;> dsimp [gapLo,gapHi] <;>
    norm_num only [mem_Icc] <;> aesop (add safe (by linarith))

theorem gap_inter_bridge_iff (C : FourRimBridgeCoordinates q B a b)
    (i : Fin 4) (j : Fin 3) (x : E) :
    x ∈ C.gap i ∩ B (C.order j).succ ↔
      (i.val = j.val ∧ x = C.map (C.lo j)) ∨
      (i.val = j.val + 1 ∧ x = C.map (C.hi j)) := by
  rw [C.bridge j]
  constructor
  · rintro ⟨⟨s,hs,hsx⟩,⟨t,ht,htx⟩⟩
    have heq := C.injective (C.gap_parameter_subset i hs)
      ⟨(C.positive j).le.trans ht.1,ht.2.trans (C.bounded j).le⟩
      (hsx.trans htx.symm)
    subst t
    rcases (C.gap_parameter_contact i j s).mp ⟨hs,ht⟩ with ⟨hij,rfl⟩ | ⟨hij,rfl⟩
    · exact Or.inl ⟨hij,hsx.symm⟩
    · exact Or.inr ⟨hij,hsx.symm⟩
  · rintro (⟨hij,rfl⟩ | ⟨hij,rfl⟩)
    · have h := (C.gap_parameter_contact i j (C.lo j)).mpr (Or.inl ⟨hij,rfl⟩)
      exact ⟨⟨_,h.1,rfl⟩,⟨_,h.2,rfl⟩⟩
    · have h := (C.gap_parameter_contact i j (C.hi j)).mpr (Or.inr ⟨hij,rfl⟩)
      exact ⟨⟨_,h.1,rfl⟩,⟨_,h.2,rfl⟩⟩

omit [FiniteDimensional ℝ E] in
private theorem zero_mem_gap_parameter_iff (C : FourRimBridgeCoordinates q B a b)
    (i : Fin 4) : (0 : ℝ) ∈ Icc (C.gapLo i) (C.gapHi i) ↔ i = 0 := by
  have hp0 := C.positive 0
  have hp1 := C.positive 1
  have hp2 := C.positive 2
  have hn0 := C.nondegenerate 0
  have hn1 := C.nondegenerate 1
  have hn2 := C.nondegenerate 2
  fin_cases i <;> dsimp [gapLo,gapHi] <;>
    norm_num only [mem_Icc] <;> aesop (add safe (by linarith))

omit [FiniteDimensional ℝ E] in
private theorem one_mem_gap_parameter_iff (C : FourRimBridgeCoordinates q B a b)
    (i : Fin 4) : (1 : ℝ) ∈ Icc (C.gapLo i) (C.gapHi i) ↔ i = 3 := by
  have hb0 := C.bounded 0
  have hb1 := C.bounded 1
  have hb2 := C.bounded 2
  have hn0 := C.nondegenerate 0
  have hn1 := C.nondegenerate 1
  have hn2 := C.nondegenerate 2
  fin_cases i <;> dsimp [gapLo,gapHi] <;>
    norm_num only [mem_Icc] <;> aesop (add safe (by linarith))

theorem gap_inter_bridge_zero_iff (C : FourRimBridgeCoordinates q B a b)
    (i : Fin 4) (x : E) :
    x ∈ C.gap i ∩ B 0 ↔ (i = 0 ∧ x = a 0) ∨ (i = 3 ∧ x = b 0) := by
  constructor
  · rintro ⟨⟨t,ht,rfl⟩,hB⟩
    have hm := C.contact.subset ⟨hB,⟨t,C.gap_parameter_subset i ht,rfl⟩⟩
    rcases hm with he | he
    · have ht0 := C.injective (C.gap_parameter_subset i ht) (by norm_num) he
      subst t
      exact Or.inl ⟨(C.zero_mem_gap_parameter_iff i).mp ht,C.zero⟩
    · have ht1 := C.injective (C.gap_parameter_subset i ht) (by norm_num) he
      subst t
      exact Or.inr ⟨(C.one_mem_gap_parameter_iff i).mp ht,C.one⟩
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · have hm : C.map 0 ∈ B 0 := (C.contact.symm.subset (by simp)).1
      exact ⟨⟨0,(C.zero_mem_gap_parameter_iff 0).mpr rfl,C.zero⟩,C.zero ▸ hm⟩
    · have hm : C.map 1 ∈ B 0 := (C.contact.symm.subset (by simp)).1
      exact ⟨⟨1,(C.one_mem_gap_parameter_iff 3).mpr rfl,C.one⟩,C.one ▸ hm⟩

def bridgeOrder (C : FourRimBridgeCoordinates q B a b) : Fin 4 ≃ Fin 4 where
  toFun := Fin.cases 0 (fun j => (C.order j).succ)
  invFun := Fin.cases 0 (fun j => (C.order.symm j).succ)
  left_inv := by
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => simp
  right_inv := by
    intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => simp

def bridgeStart (C : FourRimBridgeCoordinates q B a b) : Fin 4 → E :=
  ![b 0,C.map (C.lo 0),C.map (C.lo 1),C.map (C.lo 2)]

def bridgeFinish (C : FourRimBridgeCoordinates q B a b) : Fin 4 → E :=
  ![a 0,C.map (C.hi 0),C.map (C.hi 1),C.map (C.hi 2)]

omit [FiniteDimensional ℝ E] in
theorem bridge_endpoints (C : FourRimBridgeCoordinates q B a b) (i : Fin 4) :
    ({C.bridgeStart i,C.bridgeFinish i} : Set E) =
      {a (C.bridgeOrder i),b (C.bridgeOrder i)} := by
  fin_cases i
  · exact pair_comm _ _
  · exact C.endpoints 0
  · exact C.endpoints 1
  · exact C.endpoints 2

theorem gap_isFinitePLBallPair_cyclic (C : FourRimBridgeCoordinates q B a b)
    (i : Fin 4) : IsFinitePLBallPair ℝ (C.gap i)
      {C.bridgeFinish i,C.bridgeStart (i+1)} := by
  have h := C.gap_isFinitePLBallPair i
  fin_cases i <;> simpa [gapLo,gapHi,bridgeStart,bridgeFinish,C.zero,C.one] using h

theorem gap_inter_bridge_cyclic_iff (C : FourRimBridgeCoordinates q B a b)
    (i j : Fin 4) (x : E) :
    x ∈ C.gap i ∩ B (C.bridgeOrder j) ↔
      (i = j ∧ x = C.bridgeFinish j) ∨
      (j = i+1 ∧ x = C.bridgeStart j) := by
  cases j using Fin.cases with
  | zero =>
    rw [show C.bridgeOrder 0 = 0 from rfl,C.gap_inter_bridge_zero_iff]
    fin_cases i <;> simp [bridgeStart,bridgeFinish]
  | succ j =>
    rw [show C.bridgeOrder j.succ = (C.order j).succ from rfl,C.gap_inter_bridge_iff]
    fin_cases i <;> fin_cases j <;> simp [bridgeStart,bridgeFinish,or_comm]

end FourRimBridgeCoordinates

end PoincareConjecture.M76.OriginalTriangleCopies
