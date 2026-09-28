import PoincareConjecture.Proofs.M02.Topology.FiniteOrderComplexPivots










set_option autoImplicit false

open scoped BigOperators

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

theorem weights_zero_of_nonnegative_coordinates
    {I : Type u} {V : Type v}
    (support : I → Finset V) (c : I → V → Real)
    (hsupport : ∀ i, (support i).Nonempty)
    (hc_nonneg : ∀ i v, 0 ≤ c i v)
    (hc_pos : ∀ i v, 0 < c i v ↔ v ∈ support i)
    (s : Finset I) (w : I → Real)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (heq : (∑ i ∈ s, w i • c i) = 0) :
    ∀ i ∈ s, w i = 0 := by
  intro i hi
  obtain ⟨v, hv⟩ := hsupport i
  have hcv : 0 < c i v := (hc_pos i v).2 hv
  have heval : (∑ k ∈ s, w k • c k) v = 0 :=
    congrArg (fun q : V → Real => q v) heq
  have heval' : ∑ k ∈ s, w k * c k v = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using heval
  have hzero : ∀ k ∈ s, w k * c k v = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun k hk => mul_nonneg (hw k hk) (hc_nonneg k v))).mp heval'
  rcases mul_eq_zero.mp (hzero i hi) with hwi | hci
  · exact hwi
  · exact (ne_of_gt hcv hci).elim

theorem nonnegative_chain_weighted_sum_unique
    {I : Type u} [PartialOrder I]
    {V : Type v}
    (support : I → Finset V) (c : I → V → Real)
    (hsupport : ∀ i, (support i).Nonempty)
    (horder : ∀ i j, i ≤ j ↔ support i ⊆ support j)
    (hc_nonneg : ∀ i v, 0 ≤ c i v)
    (hc_pos : ∀ i v, 0 < c i v ↔ v ∈ support i)
    (s : Finset I) (w w' : I → Real)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∀ i ∈ s, 0 ≤ w' i)
    (hchain : ∀ i ∈ s, ∀ j ∈ s, w i ≠ 0 → w j ≠ 0 → i ≤ j ∨ j ≤ i)
    (hchain' : ∀ i ∈ s, ∀ j ∈ s, w' i ≠ 0 → w' j ≠ 0 → i ≤ j ∨ j ≤ i)
    (heq : (∑ i ∈ s, w i • c i) = ∑ i ∈ s, w' i • c i) :
    ∀ i ∈ s, w i = w' i := by
  classical
  let hstrict : ∀ {i j : I}, i < j → support i ⊂ support j := by
    intro i j hij
    refine ⟨(horder i j).mp hij.le, ?_⟩
    intro hsub
    exact (not_le_of_gt hij) ((horder j i).mpr hsub)
  refine Finset.strongInduction
    (p := fun t => ∀ (a a' : I → Real),
      (∀ i ∈ t, 0 ≤ a i) → (∀ i ∈ t, 0 ≤ a' i) →
      (∀ i ∈ t, ∀ j ∈ t, a i ≠ 0 → a j ≠ 0 → i ≤ j ∨ j ≤ i) →
      (∀ i ∈ t, ∀ j ∈ t, a' i ≠ 0 → a' j ≠ 0 → i ≤ j ∨ j ≤ i) →
      (∑ i ∈ t, a i • c i) = ∑ i ∈ t, a' i • c i →
      ∀ i ∈ t, a i = a' i)
    (fun t ih a a' ha ha' hca hca' heqa => by
      let A : Finset I := t.filter (fun i => a i ≠ 0)
      let B : Finset I := t.filter (fun i => a' i ≠ 0)
      have hAchain : ∀ i ∈ A, ∀ j ∈ A, i ≤ j ∨ j ≤ i := by
        intro i hi j hj
        exact hca i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
          (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
      have hBchain : ∀ i ∈ B, ∀ j ∈ B, i ≤ j ∨ j ≤ i := by
        intro i hi j hj
        exact hca' i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
          (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
      by_cases hAempty : A = ∅
      · have hazero : ∀ i ∈ t, a i = 0 := by
          intro i hi
          by_contra hne
          have hmem : i ∈ A := Finset.mem_filter.mpr ⟨hi, hne⟩
          simp [hAempty] at hmem
        have hsum : (∑ i ∈ t, a' i • c i) = 0 := by
          rw [← heqa]
          apply Finset.sum_eq_zero
          intro i hi
          simp [hazero i hi]
        have ha'zero := weights_zero_of_nonnegative_coordinates support c hsupport
          hc_nonneg hc_pos t a' ha' hsum
        intro i hi
        exact (hazero i hi).trans (ha'zero i hi).symm
      · have hAnonempty : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hAempty
        by_cases hBempty : B = ∅
        · have hbzero : ∀ i ∈ t, a' i = 0 := by
            intro i hi
            by_contra hne
            have hmem : i ∈ B := Finset.mem_filter.mpr ⟨hi, hne⟩
            simp [hBempty] at hmem
          have hsum : (∑ i ∈ t, a i • c i) = 0 := by
            rw [heqa]
            apply Finset.sum_eq_zero
            intro i hi
            simp [hbzero i hi]
          have hazero := weights_zero_of_nonnegative_coordinates support c hsupport
            hc_nonneg hc_pos t a ha hsum
          intro i hi
          exact (hazero i hi).trans (hbzero i hi).symm
        · have hBnonempty : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hBempty
          obtain ⟨ia, hia⟩ := Finset.exists_maximal hAnonempty
          obtain ⟨ib, hib⟩ := Finset.exists_maximal hBnonempty
          have hiaA : ia ∈ A := hia.1
          have hibB : ib ∈ B := hib.1
          have hmaxA : ∀ k ∈ A, k ≤ ia := by
            intro k hk
            rcases hAchain k hk ia hiaA with hki | hik
            · exact hki
            · exact hia.2 hk hik
          have hmaxB : ∀ k ∈ B, k ≤ ib := by
            intro k hk
            rcases hBchain k hk ib hibB with hki | hik
            · exact hki
            · exact hib.2 hk hik
          have hia_t : ia ∈ t := (Finset.mem_filter.mp hiaA).1
          have hib_t : ib ∈ t := (Finset.mem_filter.mp hibB).1
          have htopAB : support ia ⊆ support ib := by
            intro v hv
            by_contra hvb
            have hRzero : ∑ k ∈ t, a' k * c k v = 0 := by
              apply Finset.sum_eq_zero
              intro k hk
              by_cases hkw : a' k = 0
              · simp [hkw]
              · have hkB : k ∈ B := Finset.mem_filter.mpr ⟨hk, hkw⟩
                have hkle : k ≤ ib := hmaxB k hkB
                have hsub := (horder k ib).mp hkle
                have hvk : v ∉ support k := fun hvk => hvb (hsub hvk)
                have hck : c k v = 0 := by
                  apply le_antisymm
                  · exact not_lt.mp (fun hpos => hvk ((hc_pos k v).mp hpos))
                  · exact hc_nonneg k v
                simp [hck]
            have hwi : 0 < a ia := by
              exact lt_of_le_of_ne (ha ia hia_t)
                (fun h => (Finset.mem_filter.mp hiaA).2 h.symm)
            have hci : 0 < c ia v := (hc_pos ia v).2 hv
            have hLpos : 0 < ∑ k ∈ t, a k * c k v := by
              have hterm : 0 < a ia * c ia v := mul_pos hwi hci
              exact lt_of_lt_of_le hterm (Finset.single_le_sum
                (fun k hk => mul_nonneg (ha k hk) (hc_nonneg k v)) hia_t)
            have heval : (∑ k ∈ t, a k • c k) v = (∑ k ∈ t, a' k • c k) v :=
              congrArg (fun q : V → Real => q v) heqa
            have heval' : (∑ k ∈ t, a k * c k v) = ∑ k ∈ t, a' k * c k v := by
              simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using heval
            have : (∑ k ∈ t, a k * c k v) = 0 := heval'.trans hRzero
            exact (ne_of_gt hLpos) this
          have htopBA : support ib ⊆ support ia := by
            intro v hv
            by_contra hva
            have hLzero : ∑ k ∈ t, a k * c k v = 0 := by
              apply Finset.sum_eq_zero
              intro k hk
              by_cases hkw : a k = 0
              · simp [hkw]
              · have hkA : k ∈ A := Finset.mem_filter.mpr ⟨hk, hkw⟩
                have hkle : k ≤ ia := hmaxA k hkA
                have hsub := (horder k ia).mp hkle
                have hvk : v ∉ support k := fun hvk => hva (hsub hvk)
                have hck : c k v = 0 := by
                  apply le_antisymm
                  · exact not_lt.mp (fun hpos => hvk ((hc_pos k v).mp hpos))
                  · exact hc_nonneg k v
                simp [hck]
            have hwi : 0 < a' ib := by
              exact lt_of_le_of_ne (ha' ib hib_t)
                (fun h => (Finset.mem_filter.mp hibB).2 h.symm)
            have hci : 0 < c ib v := (hc_pos ib v).2 hv
            have hRpos : 0 < ∑ k ∈ t, a' k * c k v := by
              have hterm : 0 < a' ib * c ib v := mul_pos hwi hci
              exact lt_of_lt_of_le hterm (Finset.single_le_sum
                (fun k hk => mul_nonneg (ha' k hk) (hc_nonneg k v)) hib_t)
            have heval : (∑ k ∈ t, a k • c k) v = (∑ k ∈ t, a' k • c k) v :=
              congrArg (fun q : V → Real => q v) heqa
            have heval' : (∑ k ∈ t, a k * c k v) = ∑ k ∈ t, a' k * c k v := by
              simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using heval
            have : (∑ k ∈ t, a' k * c k v) = 0 := hLzero ▸ heval'.symm
            exact (ne_of_gt hRpos) this
          have hiab : ia = ib := by
            apply le_antisymm
            · exact (horder ia ib).mpr htopAB
            · exact (horder ib ia).mpr htopBA
          have hstrictA := exists_chain_coordinate_pivot_of_strict_supports
            support hsupport hstrict A hAnonempty hAchain
          obtain ⟨ip, hip, vp, hvp, hvnot⟩ := hstrictA
          have hip_eq : ip = ia := by
            by_contra hne
            have hle : ip ≤ ia := hmaxA ip hip
            have hlt : ip < ia := lt_of_le_of_ne hle hne
            obtain ⟨hsub, _⟩ := hstrict hlt
            exact hvnot ia hiaA (Ne.symm hne) (hsub hvp)
          have hstrictB := exists_chain_coordinate_pivot_of_strict_supports
            support hsupport hstrict B hBnonempty hBchain
          obtain ⟨jp, hjp, vq, hvq, hvnot'⟩ := hstrictB
          have hjp_eq : jp = ib := by
            by_contra hne
            have hle : jp ≤ ib := hmaxB jp hjp
            have hlt : jp < ib := lt_of_le_of_ne hle hne
            obtain ⟨hsub, _⟩ := hstrict hlt
            exact hvnot' ib hibB (Ne.symm hne) (hsub hvq)
          subst ib
          subst jp
          subst ip
          have hia_pos : 0 < c ia vp := (hc_pos ia vp).2 hvp
          have hsumA : ∑ k ∈ t, a k * c k vp = a ia * c ia vp := by
            apply Finset.sum_eq_single ia
            · intro k hk hki
              by_cases hkw : a k = 0
              · simp [hkw]
              · have hkA : k ∈ A := Finset.mem_filter.mpr ⟨hk, hkw⟩
                have hnotk : vp ∉ support k := hvnot k hkA hki
                have hck : c k vp = 0 := by
                  apply le_antisymm
                  · exact not_lt.mp (fun hpos => hnotk ((hc_pos k vp).mp hpos))
                  · exact hc_nonneg k vp
                simp [hck]
            · intro hia_not
              exact (hia_not hia_t).elim
          have hsumB_le : a' ia * c ia vp ≤ ∑ k ∈ t, a' k * c k vp :=
            Finset.single_le_sum
              (fun k hk => mul_nonneg (ha' k hk) (hc_nonneg k vp)) hia_t
          have heval : (∑ k ∈ t, a k • c k) vp = (∑ k ∈ t, a' k • c k) vp :=
            congrArg (fun q : V → Real => q vp) heqa
          have heval' : (∑ k ∈ t, a k * c k vp) = ∑ k ∈ t, a' k * c k vp := by
            simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using heval
          have hle : a' ia * c ia vp ≤ a ia * c ia vp := by
            calc
              a' ia * c ia vp ≤ ∑ k ∈ t, a' k * c k vp := hsumB_le
              _ = ∑ k ∈ t, a k * c k vp := heval'.symm
              _ = a ia * c ia vp := hsumA
          have htop_le : a' ia ≤ a ia := le_of_mul_le_mul_right hle hia_pos
          have hsumB : ∑ k ∈ t, a' k * c k vq = a' ia * c ia vq := by
            apply Finset.sum_eq_single ia
            · intro k hk hki
              by_cases hkw : a' k = 0
              · simp [hkw]
              · have hkB : k ∈ B := Finset.mem_filter.mpr ⟨hk, hkw⟩
                have hnotk : vq ∉ support k := hvnot' k hkB hki
                have hck : c k vq = 0 := by
                  apply le_antisymm
                  · exact not_lt.mp (fun hpos => hnotk ((hc_pos k vq).mp hpos))
                  · exact hc_nonneg k vq
                simp [hck]
            · intro hia_not
              exact (hia_not hia_t).elim
          have hsumA_le : a ia * c ia vq ≤ ∑ k ∈ t, a k * c k vq :=
            Finset.single_le_sum
              (fun k hk => mul_nonneg (ha k hk) (hc_nonneg k vq)) hia_t
          have hevalq : (∑ k ∈ t, a k • c k) vq = (∑ k ∈ t, a' k • c k) vq :=
            congrArg (fun q : V → Real => q vq) heqa
          have hevalq' : (∑ k ∈ t, a k * c k vq) = ∑ k ∈ t, a' k * c k vq := by
            simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hevalq
          have hle' : a ia * c ia vq ≤ a' ia * c ia vq := by
            calc
              a ia * c ia vq ≤ ∑ k ∈ t, a k * c k vq := hsumA_le
              _ = ∑ k ∈ t, a' k * c k vq := hevalq'
              _ = a' ia * c ia vq := hsumB
          have htop_le' : a ia ≤ a' ia :=
            le_of_mul_le_mul_right hle' ((hc_pos ia vq).2 hvq)
          have htop_eq : a ia = a' ia := le_antisymm htop_le' htop_le
          have heq_erase : (∑ k ∈ t.erase ia, a k • c k) =
              ∑ k ∈ t.erase ia, a' k • c k := by
            have hsumAfull := Finset.sum_erase_add t (fun k => a k • c k) hia_t
            have hsumBfull := Finset.sum_erase_add t (fun k => a' k • c k) hia_t
            have hboth :
                (∑ k ∈ t.erase ia, a k • c k) + a ia • c ia =
                  (∑ k ∈ t.erase ia, a' k • c k) + a ia • c ia := by
              calc
                (∑ k ∈ t.erase ia, a k • c k) + a ia • c ia =
                    ∑ k ∈ t, a k • c k := hsumAfull
                _ = ∑ k ∈ t, a' k • c k := heqa
                _ = (∑ k ∈ t.erase ia, a' k • c k) + a' ia • c ia := hsumBfull.symm
                _ = (∑ k ∈ t.erase ia, a' k • c k) + a ia • c ia := by rw [htop_eq]
            exact add_right_cancel hboth
          have hsub := ih (t.erase ia) (Finset.erase_ssubset hia_t)
            a a' (fun k hk => ha k (Finset.mem_of_mem_erase hk))
            (fun k hk => ha' k (Finset.mem_of_mem_erase hk))
            (fun k hk l hl hkw hlw => hca k (Finset.mem_of_mem_erase hk)
              l (Finset.mem_of_mem_erase hl) hkw hlw)
            (fun k hk l hl hkw hlw => hca' k (Finset.mem_of_mem_erase hk)
              l (Finset.mem_of_mem_erase hl) hkw hlw) heq_erase
          intro k hk
          by_cases hki : k = ia
          · exact hki ▸ htop_eq
          · exact hsub k (Finset.mem_erase.mpr ⟨hki, hk⟩))
    s w w' hw hw' hchain hchain' heq

theorem finiteOrderComplexMap_injective_of_supports
    {I : Type u} [PartialOrder I] [Fintype I]
    {V : Type v} [Fintype V] (c : I → V → Real) (support : I → Finset V)
    (hsupport : ∀ i, (support i).Nonempty)
    (horder : ∀ i j, i ≤ j ↔ support i ⊆ support j)
    (hc_nonneg : ∀ i v, 0 ≤ c i v)
    (hc_pos : ∀ i v, 0 < c i v ↔ v ∈ support i) :
    Function.Injective (finiteOrderComplexMap I c) := by
  intro z z' heq
  apply Subtype.ext
  funext i
  have hz := (finiteOrderComplex_space I z.val).mp z.property
  have hz' := (finiteOrderComplex_space I z'.val).mp z'.property
  have heq' :
      (∑ k ∈ (Finset.univ : Finset I), z.val k • c k) =
        ∑ k ∈ (Finset.univ : Finset I), z'.val k • c k := by
    simpa [finiteOrderComplexMap_apply] using heq
  have huniq := nonnegative_chain_weighted_sum_unique support c hsupport horder
    hc_nonneg hc_pos (Finset.univ : Finset I) z.val z'.val
    (fun k hk => hz.1 k) (fun k hk => hz'.1 k)
    (fun k hk l hl hkw hlw => hz.2.2 k l hkw hlw)
    (fun k hk l hl hkw hlw => hz'.2.2 k l hkw hlw) heq'
  exact huniq i (Finset.mem_univ i)

theorem finiteOrderComplex_space_isCompact
    {I : Type u} [PartialOrder I] [Fintype I] :
    IsCompact ((finiteOrderComplex I).space) := by
  let K := finiteOrderComplex I
  have hfinite : K.faces.Finite := finiteOrderComplex_finite I
  let : Finite K.faces := hfinite.to_subtype
  have hspace : K.space = ⋃ s : K.faces, convexHull ℝ (s.val : Set (I → Real)) := by
    ext x
    simp [Geometry.SimplicialComplex.space]
  rw [hspace]
  apply isCompact_iUnion
  intro s
  apply Set.Finite.isCompact_convexHull ℝ
  exact s.val.finite_toSet

noncomputable def finiteOrderComplexMap_homeomorph_range_of_supports
    {I : Type u} [PartialOrder I] [Fintype I]
    {V : Type v} [Fintype V] (c : I → V → Real) (support : I → Finset V)
    (hsupport : ∀ i, (support i).Nonempty)
    (horder : ∀ i j, i ≤ j ↔ support i ⊆ support j)
    (hc_nonneg : ∀ i v, 0 ≤ c i v)
    (hc_pos : ∀ i v, 0 < c i v ↔ v ∈ support i) :
    (finiteOrderComplex I).space ≃ₜ Set.range (finiteOrderComplexMap I c) := by
  let K := finiteOrderComplex I
  have hcomp : IsCompact K.space := finiteOrderComplex_space_isCompact (I := I)
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp hcomp
  let e : K.space ≃ Set.range (finiteOrderComplexMap I c) :=
    Equiv.ofInjective (finiteOrderComplexMap I c)
      (finiteOrderComplexMap_injective_of_supports c support hsupport horder hc_nonneg hc_pos)
  exact Continuous.homeoOfEquivCompactToT2 (f := e)
    (Continuous.subtype_mk (finiteOrderComplexMap I c).continuous
      (fun z => Set.mem_range_self z))

end PoincareConjecture.Proofs.M02.Topology
