import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskIntervalHalfProduct
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSignedDiskCut










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "I" => Icc (-1 : ℝ) 1
local notation "I+" => Icc (0 : ℝ) 1
local notation "I-" => Icc (-1 : ℝ) 0

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem exists_signed_interval_product {N Q B : Set E} (a : Bool → E)
    (hN : IsFinitePLBallPair (ℝ × ℝ) N Q)
    (hB : IsFinitePLBallPair ℝ B {a false, a true}) (ha : a false ≠ a true)
    (f : E → ℝ) (hf : ContinuousOn f N)
    (hzero : N ∩ {x | f x = 0} = B)
    (hqzero : Q ∩ {x | f x = 0} = {a false, a true})
    (F : Bool → ℝ → E) (hF : ∀ i, FinitePiecewiseAffineOn (F i) I)
    (hi : ∀ i, InjOn (F i) I) (hFa : ∀ i, F i 0 = a i)
    (hFQ : ∀ i, F i '' I ⊆ Q)
    (hdis : Disjoint (F false '' I) (F true '' I))
    (hFpos : ∀ i t, t ∈ I → (0 ≤ f (F i t) ↔ 0 ≤ t))
    (hFneg : ∀ i t, t ∈ I → (f (F i t) ≤ 0 ↔ t ≤ 0)) :
    ∃ H : (B ×ˢ I : Set (E × ℝ)) ≃ₜ N, H.IsFinitePL ∧
      (∀ x : B, (H ⟨((x : E), 0), x.property, by norm_num⟩ : E) = x) ∧
      (∀ i (t : I), (H ⟨(a i, (t : ℝ)), by
        refine ⟨hB.1 ?_, t.property⟩
        cases i <;> simp⟩ : E) = F i t) ∧
      (∀ x : (B ×ˢ I : Set (E × ℝ)), (H x : E) ∈ Q ↔
        (x : E × ℝ).1 ∈ ({a false, a true} : Set E) ∨
          (x : E × ℝ).2 ∈ ({-1, 1} : Set ℝ)) ∧
      (∀ x : (B ×ˢ I : Set (E × ℝ)), 0 ≤ f (H x) ↔ 0 ≤ (x : E × ℝ).2) ∧
      ∀ x : (B ×ˢ I : Set (E × ℝ)), f (H x) ≤ 0 ↔ (x : E × ℝ).2 ≤ 0 := by
  let Nm := N ∩ {x | f x ≤ 0}
  let Np := N ∩ {x | 0 ≤ f x}
  let Qm := Q ∩ {x | f x ≤ 0}
  let Qp := Q ∩ {x | 0 ≤ f x}
  have hBN : B ⊆ N := fun _ hx => (hzero.symm.subset hx).1
  have hBzero : ∀ x ∈ B, f x = 0 := fun _ hx => (hzero.symm.subset hx).2
  have hBQ : B ∩ Q = {a false, a true} := by
    apply Subset.antisymm
    · exact fun x hx => hqzero.subset ⟨hx.2, hBzero x hx.1⟩
    · intro x hx
      have hz := hqzero.symm.subset hx
      exact ⟨hzero.subset ⟨hN.1 hz.1, hz.2⟩, hz.1⟩
  have hm : ∃ x ∈ Q, f x < 0 := by
    refine ⟨F false (-1), hFQ false ⟨-1, by norm_num, rfl⟩, ?_⟩
    exact lt_of_not_ge (fun h => by
      have := (hFpos false (-1) (by norm_num)).mp h
      norm_num at this)
  have hp : ∃ x ∈ Q, 0 < f x := by
    refine ⟨F false 1, hFQ false ⟨1, by norm_num, rfl⟩, ?_⟩
    exact lt_of_not_ge (fun h => by
      have := (hFneg false 1 (by norm_num)).mp h
      norm_num at this)
  have hcuts := hN.signed_halves_of_zero_arc f hf hB ha hzero hqzero hm hp
  obtain ⟨U, V, hU, hV, hUV, _⟩ := hN.exists_boundary_arcs
    (hqzero.symm.subset (Or.inl rfl)).1 (hqzero.symm.subset (Or.inr rfl)).1 ha
  have hrims := isFinitePLBallPair_signed_halves_of_arcs hU hV hUV f
    (hf.mono hN.1) hqzero hm hp
  have hBm : B ∩ Qm = {a false, a true} := by
    ext x
    constructor
    · exact fun hx => hBQ.subset ⟨hx.1, hx.2.1⟩
    · intro hx
      have h := hBQ.symm.subset hx
      exact ⟨h.1, h.2, (hBzero x h.1).le⟩
  have hBp : B ∩ Qp = {a false, a true} := by
    ext x
    constructor
    · exact fun hx => hBQ.subset ⟨hx.1, hx.2.1⟩
    · intro hx
      have h := hBQ.symm.subset hx
      exact ⟨h.1, h.2, (hBzero x h.1).ge⟩
  have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have hcopy := hI
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ := hcopy
  have hIplus : I+ ⊆ I := fun _ hx => ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans hx.1, hx.2⟩
  have hFp (i : Bool) : FinitePiecewiseAffineOn (F i) I+ := by
    rw [← hKI]
    exact (hF i).restrict K hK (hKI.subset.trans hIplus)
  let r : ℝ →ᴬ[ℝ] ℝ := -(ContinuousAffineMap.id ℝ ℝ)
  have hr : FinitePiecewiseAffineOn r I+ := ⟨K, hK, hKI, K.affineOnFaces_affine r⟩
  have hrI : MapsTo r I+ I := by
    intro t ht
    change -t ∈ I
    constructor <;> linarith [ht.1, ht.2]
  let Fm : Bool → ℝ → E := fun i t => F i (-t)
  have hFm (i : Bool) : FinitePiecewiseAffineOn (Fm i) I+ := (hF i).comp hr hrI
  have him (i : Bool) : InjOn (Fm i) I+ := by
    intro x hx y hy hxy
    exact neg_injective (hi i (hrI hx) (hrI hy) hxy)
  have hFpm (i : Bool) : F i '' I+ ⊆ Qp := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨hFQ i ⟨t, hIplus ht, rfl⟩, (hFpos i t (hIplus ht)).mpr ht.1⟩
  have hFmm (i : Bool) : Fm i '' I+ ⊆ Qm := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨hFQ i ⟨-t, hrI ht, rfl⟩,
      (hFneg i (-t) (hrI ht)).mpr (neg_nonpos.mpr ht.1)⟩
  have hFmsub (i : Bool) : Fm i '' I+ ⊆ F i '' I := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨-t, hrI ht, rfl⟩
  have hNmp : IsFinitePLBallPair (ℝ × ℝ) Nm (B ∪ Qm) := by
    simpa only [union_comm] using hcuts.1
  obtain ⟨P, hP, hP0, hPF, hPQ, hPB⟩ := exists_interval_half_product a hB ha
    hcuts.2 hrims.2 hBp (show (0 : ℝ) < 1 by norm_num) F hFp
    (fun i => (hi i).mono hIplus) hFa hFpm
    (hdis.mono (image_mono hIplus) (image_mono hIplus))
  obtain ⟨M, hM, hM0, hMF, hMQ, hMB⟩ := exists_interval_half_product a hB ha
    hNmp hrims.1 hBm (show (0 : ℝ) < 1 by norm_num) Fm hFm him
    (by intro i; simpa only [Fm, neg_zero] using hFa i) hFmm
    (hdis.mono (hFmsub false) (hFmsub true))
  let j : E × ℝ →ᴬ[ℝ] E × ℝ :=
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap.prod
      (-(ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap)
  have hnegball := hB.prod (isFinitePLBallPair_Icc (show (-1 : ℝ) < 0 by norm_num))
  have hncopy := hnegball
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLs, _⟩, _⟩, _⟩ := hncopy
  have hj : FinitePiecewiseAffineOn j (B ×ˢ I-) :=
    ⟨L, hL, hLs, L.affineOnFaces_affine j⟩
  have hji : InjOn j (B ×ˢ I-) := by
    intro x _ y _ h
    change (x.1, -x.2) = (y.1, -y.2) at h
    have hfirst := congrArg (fun z : E × ℝ => z.1) h
    have hsecond := congrArg (fun z : E × ℝ => z.2) h
    apply Prod.ext
    · exact hfirst
    · exact neg_injective hsecond
  have hjimage : j '' (B ×ˢ I-) = B ×ˢ I+ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨hy.1, ?_⟩
      change -y.2 ∈ I+
      constructor <;> linarith [hy.2.1, hy.2.2]
    · rintro ⟨hx, ht⟩
      refine ⟨(x.1, -x.2), ⟨hx, ?_⟩, ?_⟩
      · constructor <;> linarith [ht.1, ht.2]
      · change (x.1, - -x.2) = x
        simp only [neg_neg, Prod.mk.eta]
  have hjex := hj.exists_homeomorph_image hji
  rw [hjimage] at hjex
  obtain ⟨J, hJ, hJval⟩ := hjex
  let M' := J.trans M
  have hM' : M'.IsFinitePL := hJ.trans hM
  have hM'0 (x : B) : (M' ⟨((x : E), 0), x.property, by norm_num⟩ : E) = x := by
    have heq : J ⟨((x : E), 0), x.property, by norm_num⟩ =
        ⟨((x : E), 0), x.property, by norm_num⟩ := by
      apply Subtype.ext
      rw [hJval]
      change ((x : E), -(0 : ℝ)) = ((x : E), 0)
      rw [neg_zero]
    change (M (J _) : E) = x
    rw [heq]
    exact hM0 x
  have hM'B (x : (B ×ˢ I- : Set (E × ℝ))) :
      (M' x : E) ∈ B ↔ (x : E × ℝ).2 = 0 := by
    change (M (J x) : E) ∈ B ↔ _
    rw [hMB, hJval]
    change -(x : E × ℝ).2 = 0 ↔ _
    exact neg_eq_zero
  have hM'Q (x : (B ×ˢ I- : Set (E × ℝ))) :
      (M' x : E) ∈ Qm ↔ (x : E × ℝ).1 ∈ ({a false, a true} : Set E) ∨
        (x : E × ℝ).2 = -1 := by
    change (M (J x) : E) ∈ Qm ↔ _
    rw [hMQ, hJval]
    change _ ∨ -(x : E × ℝ).2 = 1 ↔ _
    exact or_congr Iff.rfl (by constructor <;> intro h <;> linarith)
  have hoverlap (x : (B ×ˢ I- : Set (E × ℝ))) :
      (x : E × ℝ) ∈ B ×ˢ I+ ↔ (M' x : E) ∈ Np := by
    have hx0 : (x : E × ℝ) ∈ B ×ˢ I+ ↔ (x : E × ℝ).2 = 0 := by
      constructor
      · exact fun h => le_antisymm x.property.2.2 h.2.1
      · intro h
        exact ⟨x.property.1, by rw [h]; norm_num⟩
    rw [hx0, ← hM'B]
    constructor
    · exact fun h => ⟨hBN h, (hBzero _ h).ge⟩
    · exact fun h => hzero.subset ⟨h.1, le_antisymm (M' x).property.2 h.2⟩
  have hagree (x : E × ℝ) (hmx : x ∈ B ×ˢ I-) (hpx : x ∈ B ×ˢ I+) :
      (M' ⟨x, hmx⟩ : E) = P ⟨x, hpx⟩ := by
    have ht : x.2 = 0 := le_antisymm hmx.2.2 hpx.2.1
    have hx : x = (x.1, 0) := Prod.ext rfl ht
    have hxM : (⟨x, hmx⟩ : (B ×ˢ I- : Set (E × ℝ))) =
        ⟨(x.1, 0), hmx.1, by norm_num⟩ := Subtype.ext hx
    have hxP : (⟨x, hpx⟩ : (B ×ˢ I+ : Set (E × ℝ))) =
        ⟨(x.1, 0), hpx.1, by norm_num⟩ := Subtype.ext hx
    rw [hxM, hxP]
    exact (hM'0 ⟨_, hmx.1⟩).trans (hP0 ⟨_, hpx.1⟩).symm
  obtain ⟨G, hG, hGM, hGP⟩ := Homeomorph.exists_union_finitePL M' P hM' hP hoverlap hagree
  have hsource : (B ×ˢ I-) ∪ (B ×ˢ I+) = B ×ˢ I := by
    ext x
    constructor
    · rintro (h | h)
      · exact ⟨h.1, h.2.1, h.2.2.trans (by norm_num)⟩
      · exact ⟨h.1, (by norm_num : (-1 : ℝ) ≤ 0).trans h.2.1, h.2.2⟩
    · intro h
      exact (le_total x.2 0).elim
        (fun ht => Or.inl ⟨h.1, h.2.1, ht⟩) (fun ht => Or.inr ⟨h.1, ht, h.2.2⟩)
  have htarget : Nm ∪ Np = N := by
    ext x
    constructor
    · exact fun h => h.elim And.left And.left
    · intro h
      exact (le_total (f x) 0).elim (fun ht => Or.inl ⟨h, ht⟩) (fun ht => Or.inr ⟨h, ht⟩)
  let H := (Homeomorph.setCongr hsource.symm).trans (G.trans (Homeomorph.setCongr htarget))
  have hH : H.IsFinitePL := hG.setCongr hsource htarget
  have hkeepM (x : (B ×ˢ I- : Set (E × ℝ))) :
      (H ⟨x, hsource.subset (Or.inl x.property)⟩ : E) = M' x := hGM x
  have hkeepP (x : (B ×ˢ I+ : Set (E × ℝ))) :
      (H ⟨x, hsource.subset (Or.inr x.property)⟩ : E) = P x := hGP x
  have hMmem := H.mem_subset_iff_of_extension M'
    (fun _ hx => hsource.subset (Or.inl hx)) inter_subset_left
    (fun x => Subtype.ext (hkeepM x))
  have hPmem := H.mem_subset_iff_of_extension P
    (fun _ hx => hsource.subset (Or.inr hx)) inter_subset_left
    (fun x => Subtype.ext (hkeepP x))
  refine ⟨H, hH, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (hkeepP ⟨((x : E), 0), x.property, by norm_num⟩).trans (hP0 x)
  · intro i t
    have hai : a i ∈ B := by apply hB.1; cases i <;> simp
    by_cases ht : 0 ≤ (t : ℝ)
    · exact (hkeepP ⟨(a i, (t : ℝ)), hai, ht, t.property.2⟩).trans
        (hPF i ⟨t, ht, t.property.2⟩)
    · have ht' : (t : ℝ) ≤ 0 := (lt_of_not_ge ht).le
      have hneg : -(t : ℝ) ∈ I+ := ⟨neg_nonneg.mpr ht', by linarith [t.property.1]⟩
      have hJt : J ⟨(a i, (t : ℝ)), hai, t.property.1, ht'⟩ =
          ⟨(a i, -(t : ℝ)), hai, hneg⟩ := Subtype.ext (hJval _)
      have hmval : (M' ⟨(a i, (t : ℝ)), hai, t.property.1, ht'⟩ : E) = F i t := by
        change (M (J ⟨(a i, (t : ℝ)), hai, t.property.1, ht'⟩) : E) = F i t
        rw [hJt]
        simpa only [Fm, neg_neg] using hMF i ⟨-(t : ℝ), hneg⟩
      exact (hkeepM ⟨(a i, (t : ℝ)), hai, t.property.1, ht'⟩).trans hmval
  · intro x
    by_cases ht : 0 ≤ (x : E × ℝ).2
    · let xp : (B ×ˢ I+ : Set (E × ℝ)) := ⟨x, x.property.1, ht, x.property.2.2⟩
      rw [hkeepP xp]
      have hmem : (P xp : E) ∈ Q ↔ (P xp : E) ∈ Qp :=
        ⟨fun h => ⟨h, (P xp).property.2⟩, And.left⟩
      rw [hmem, hPQ]
      change ((x : E × ℝ).1 ∈ ({a false, a true} : Set E) ∨ (x : E × ℝ).2 = 1) ↔ _ ∨
        (x : E × ℝ).2 = -1 ∨ (x : E × ℝ).2 = 1
      have hn : (x : E × ℝ).2 ≠ -1 := by linarith
      simp only [hn, false_or]
    · have ht' : (x : E × ℝ).2 ≤ 0 := (lt_of_not_ge ht).le
      let xm : (B ×ˢ I- : Set (E × ℝ)) := ⟨x, x.property.1, x.property.2.1, ht'⟩
      rw [hkeepM xm]
      have hmem : (M' xm : E) ∈ Q ↔ (M' xm : E) ∈ Qm :=
        ⟨fun h => ⟨h, (M' xm).property.2⟩, And.left⟩
      rw [hmem, hM'Q]
      change ((x : E × ℝ).1 ∈ ({a false, a true} : Set E) ∨ (x : E × ℝ).2 = -1) ↔ _ ∨
        (x : E × ℝ).2 = -1 ∨ (x : E × ℝ).2 = 1
      have hn : (x : E × ℝ).2 ≠ 1 := by linarith
      simp only [hn, or_false]
  · intro x
    have h := hPmem x
    change ((x : E × ℝ).1 ∈ B ∧ (x : E × ℝ).2 ∈ I+) ↔
      ((H x : E) ∈ N ∧ 0 ≤ f (H x)) at h
    simpa only [mem_Icc, x.property.1, x.property.2.2, (H x).property,
      true_and, and_true] using h.symm
  · intro x
    have h := hMmem x
    change ((x : E × ℝ).1 ∈ B ∧ (x : E × ℝ).2 ∈ I-) ↔
      ((H x : E) ∈ N ∧ f (H x) ≤ 0) at h
    simpa only [mem_Icc, x.property.1, x.property.2.1, (H x).property,
      true_and] using h.symm

end PoincareConjecture.M76.HamiltonIndexOne
