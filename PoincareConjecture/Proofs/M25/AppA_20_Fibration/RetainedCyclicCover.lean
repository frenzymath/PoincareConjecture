import PoincareConjecture.Proofs.M25.AppA_20_Fibration.NonseparatingCompactUnion
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.ReturnOverlapGeometry
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SameUpToReversalTransport

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem exists_retained_cyclic_cover_of_nonseparating :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 → H.X = Set.univ →
      ∀ (N : EpsilonNeck g), N ∈ H.necks → N.IsNonseparating →
      ∃ (n : ℕ) (K : Fin (n + 1) → EpsilonNeck g) (a b : Fin (n + 1) → ℝ),
        (∀ i, K i ∈ H.necks ∨ (K i).reverse ∈ H.necks) ∧
        (∀ i, (K i).epsilon = H.epsilon) ∧
        (∀ i, -(K i).epsilon⁻¹ < a i) ∧ (∀ i, b i < (K i).epsilon⁻¹) ∧
        (∀ i x, x ∈ (K i).carrier →
          ∃ j, x ∈ (K j).carrier ∧
            ((K j).coordinate_inverse x).2 ∈ Icc (a j) (b j)) ∧
        (⋃ i, (K i).carrier) = Set.univ ∧
        (∀ i, ((K i).carrier ∩ (K (i + 1)).carrier).Nonempty) := by
  obtain ⟨ec, hcp, hccap, compactReturn⟩ :=
    NeckOnlyCover.exists_compact_whole_union_of_nonseparating.{u}
  obtain ⟨eg, hgp, _, closingGeometry⟩ := NeckOnlyCover.exists_closing_return_geometry.{u}
  refine ⟨min ec eg, lt_min hcp hgp, (min_le_left _ _).trans hccap, ?_⟩
  intro M _ _ _ _ _ _ g H hsmall hwhole N hN hnonsep
  classical
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let L : ℝ := H.epsilon⁻¹
  have hL : 0 < L := inv_pos.mpr H.epsilon_pos
  obtain ⟨m, C, R, _P0, _Q0, hshape, hsource, hstart, _hquarters,
    _hhistory, _hincidence, hRsource, heR, _hRfrontier, hRout, hRpositive,
    hreturn, _hP0, _hQ0, _heQ0, _hQ0center, _hwholeOld, _hcompactOld⟩ :=
    compactReturn H (hsmall.trans (min_le_left _ _)) hwhole N hN hnonsep
  have hreturn' : ∀ c ∈ Ioo (-L) 0,
      ¬ Disjoint R.carrier ((C.neck 0).region (-L) c) := by
    simpa only [hstart] using hreturn
  obtain ⟨P, Q, Rh, _f, _hN, _hR, lo, rlo, rhi, hP, hQP, hRh, heQ, _heRh,
    hQcenter, _hfs, _hfbound, _hgraph, _hNs, _hNbound, _hNgraph,
    _hRs, _hRbound, _hRgraph, _hNband, hRband,
    _hTNsource, _hTNtarget, _hTNs, _hTNinvs, _hTNforward, _hTNinverse,
    _hTRsource, _hTRtarget, _hTRs, _hTRinvs, _hTRforward, _hTRinverse,
    hlo, _hlo0, hrlo, _hrorder, hrhi, hcovered⟩ :=
    closingGeometry H (hsmall.trans (min_le_right _ _)) hwhole C 0 (m : ℤ)
      hshape R heR hRpositive hRout hreturn'
  have hactive (j : ℤ) : j ∈ C.shape.active ↔ j ∈ Icc 0 (m : ℤ) := by
    rw [hshape]; rfl
  have hact (j : ℕ) (hj : j ≤ m) : (j : ℤ) ∈ C.shape.active :=
    (hactive _).mpr ⟨by omega, by exact_mod_cast hj⟩
  let I := Fin (m + 3)
  let W (i : I) : EpsilonNeck g :=
    if i.val ≤ m then C.neck (i.val : ℤ) else if i.val = m + 1 then R else Q
  let alpha (i : I) : ℝ :=
    if i.val ≤ m then lo (i.val : ℤ) else if i.val = m + 1 then rlo else -(19 * L / 20)
  let beta (i : I) : ℝ :=
    if i.val ≤ m then 3 * L / 4 else if i.val = m + 1 then rhi else 19 * L / 20
  have heW (i : I) : (W i).epsilon = H.epsilon := by
    dsimp only [W]
    split_ifs with hi hi
    · exact C.epsilon_eq _ (hact _ hi)
    · exact heR
    · exact heQ
  have halpha (i : I) : -(W i).epsilon⁻¹ < alpha i := by
    rw [heW]
    change -L < alpha i
    dsimp only [alpha]
    split_ifs with hi hi
    · exact (hlo _ (hact _ hi)).1
    · exact hrlo
    · linarith
  have hbeta (i : I) : beta i < (W i).epsilon⁻¹ := by
    rw [heW]
    change beta i < L
    dsimp only [beta]
    split_ifs
    · linarith
    · exact hrhi
    · linarith
  have reindex (T : EpsilonNeck g → ℝ → ℝ → Set M) :
      (⋃ i : I, T (W i) (alpha i) (beta i)) =
        ((⋃ j ∈ C.shape.active, T (C.neck j) (lo j) (3 * L / 4)) ∪
          T R rlo rhi) ∪ T Q (-(19 * L / 20)) (19 * L / 20) := by
    ext x
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      by_cases hic : i.val ≤ m
      · exact Or.inl (Or.inl ⟨(i.val : ℤ), hact _ hic,
          by simpa only [W, alpha, beta, if_pos hic] using hi⟩)
      · by_cases hir : i.val = m + 1
        · exact Or.inl (Or.inr
            (by simpa only [W, alpha, beta, if_neg hic, if_pos hir] using hi))
        · exact Or.inr
            (by simpa only [W, alpha, beta, if_neg hic, if_neg hir] using hi)
    · rintro ((⟨j, hj, hx⟩ | hx) | hx)
      · have hjrange := (hactive j).mp hj
        have hjcast : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hjrange.1
        have hjm : j.toNat ≤ m := by have := hjrange.2; omega
        let i : I := ⟨j.toNat, by omega⟩
        refine ⟨i, ?_⟩
        simpa only [W, alpha, beta, i, if_pos hjm, hjcast] using hx
      · let i : I := ⟨m + 1, by omega⟩
        refine ⟨i, ?_⟩
        simpa only [W, alpha, beta, i, if_neg (show ¬m + 1 ≤ m by omega),
          if_pos (rfl : m + 1 = m + 1), ite_true] using hx
      · let i : I := ⟨m + 2, by omega⟩
        refine ⟨i, ?_⟩
        simpa only [W, alpha, beta, i, if_neg (show ¬m + 2 ≤ m by omega),
          if_neg (show ¬m + 2 = m + 1 by omega)] using hx
  have hretained : (⋃ i : I, (W i).carrier) =
      ⋃ i : I, (W i).coordinate_map '' (univ ×ˢ Icc (alpha i) (beta i)) := by
    rw [reindex (fun A _ _ => A.carrier),
      reindex (fun A a b => A.coordinate_map '' (univ ×ˢ Icc a b))]
    exact hcovered
  have hrawCover (i : I) (x : M) (hx : x ∈ (W i).carrier) :
      ∃ j, x ∈ (W j).carrier ∧
        ((W j).coordinate_inverse x).2 ∈ Icc (alpha j) (beta j) := by
    have hu : x ∈ ⋃ j : I, (W j).carrier := mem_iUnion.mpr ⟨i, hx⟩
    rw [hretained] at hu
    obtain ⟨j, z, hz, rfl⟩ := mem_iUnion.mp hu
    have hstrip : z.2 ∈ Ioo (-(W j).epsilon⁻¹) (W j).epsilon⁻¹ :=
      ⟨(halpha j).trans_le hz.2.1, hz.2.2.trans_lt (hbeta j)⟩
    exact ⟨j, (W j).coordinate_map_mem ⟨hz.1, hstrip⟩,
      by simpa only [(W j).coordinate_inverse_map z hstrip] using hz.2⟩
  have hreflexive (A : EpsilonNeck g) : A.SameUpToReversal A := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, 1, Or.inl rfl, ?_⟩
    intro z _
    simp only [one_mul, Prod.eta]
  have hrepresentative (i : I) : ∃ A ∈ H.necks, (W i).SameUpToReversal A := by
    dsimp only [W]
    split_ifs with hi hi
    · obtain ⟨A, hA, hrel⟩ := C.selected _ (hact _ hi)
      exact ⟨A, hsource ▸ hA, hrel⟩
    · exact ⟨R, hRsource, hreflexive R⟩
    · refine ⟨P, hP, ?_⟩
      rcases hQP with h | h
      · rw [h]; exact hreflexive P
      · rw [h]
        refine ⟨rfl, rfl, rfl, rfl, rfl, -1, Or.inr rfl, ?_⟩
        intro z _
        change P.coordinate_map (z.1, -z.2) = P.coordinate_map (z.1, -1 * z.2)
        rw [neg_one_mul]
  choose K hK hrel using hrepresentative
  have htransport (i : I) :=
    (W i).exists_signed_retained_interval_of_sameUpToReversal (K i) (hrel i)
      (alpha i) (beta i) (halpha i) (hbeta i)
  choose sigma a b _hsign heK _hscale _hcenter hcarrier _hsphere ha hb
    _horder _hinverse _hslab hheight using htransport
  have hcover (i : I) (x : M) (hx : x ∈ (K i).carrier) :
      ∃ j, x ∈ (K j).carrier ∧
        ((K j).coordinate_inverse x).2 ∈ Icc (a j) (b j) := by
    obtain ⟨j, hj, ht⟩ := hrawCover i x ((hcarrier i) ▸ hx)
    exact ⟨j, (hcarrier j).symm ▸ hj, (hheight j x hj).mp ht⟩
  have hoverlap (i : I) : ((W i).carrier ∩ (W (i + 1)).carrier).Nonempty := by
    by_cases hi : i.val < m
    · have hnext : (i + 1).val = i.val + 1 :=
        Fin.val_add_one_of_lt' (by omega)
      have hi0 : i.val ≤ m := by omega
      have hi1 : (i + 1).val ≤ m := by omega
      have hia : (i.val : ℤ) ∈ C.shape.active := hact _ hi0
      have hib : (i.val : ℤ) + 1 ∈ C.shape.active := by
        simpa only [Nat.cast_add, Nat.cast_one] using hact (i.val + 1) (by omega)
      simpa only [W, if_pos hi0, if_pos hi1, hnext, Nat.cast_add, Nat.cast_one]
        using C.adjacent_overlap _ hia hib
    · by_cases him : i.val = m
      · have hnext : (i + 1).val = m + 1 := by
          rw [Fin.val_add_one_of_lt' (by omega), him]
        have hRc : R.center ∈ R.carrier :=
          R.central_sphere_subset R.center_on_central_sphere
        obtain ⟨x, hxR, hxB⟩ :=
          mem_closure_iff.mp hRpositive R.carrier R.carrier_open hRc
        have hx : x ∈ (C.neck (m : ℤ)).carrier ∩ R.carrier := ⟨hxB.1, hxR⟩
        refine ⟨x, ?_⟩
        simpa only [W, him, hnext, if_pos (le_refl m),
          if_neg (show ¬m + 1 ≤ m by omega),
          if_pos (rfl : m + 1 = m + 1), ite_true] using hx
      · by_cases hir : i.val = m + 1
        · have hnext : (i + 1).val = m + 2 := by
            rw [Fin.val_add_one_of_lt' (by omega), hir]
          let q0 := ((C.neck 0).coordinate_inverse (C.neck 0).center).1
          let x := Q.coordinate_map (q0, -L / 4)
          have hxRh : x ∈ Rh.carrier := (hRband q0 (-L / 4)
            ⟨by linarith, by linarith⟩).1
          have hxR : x ∈ R.carrier := by
            rcases hRh with h | h
            · simpa only [h] using hxRh
            · simpa only [h, EpsilonNeck.reverse] using hxRh
          have hxQ : x ∈ Q.carrier := by
            apply Q.coordinate_map_mem
            refine ⟨mem_univ _, ?_⟩
            rw [heQ]
            change -L < -L / 4 ∧ -L / 4 < L
            constructor <;> linarith
          refine ⟨x, ?_⟩
          simpa only [W, hir, hnext, if_neg (show ¬m + 1 ≤ m by omega),
            if_pos (rfl : m + 1 = m + 1), ite_true, mem_inter_iff,
            if_neg (show ¬m + 2 ≤ m by omega),
            if_neg (show ¬m + 2 = m + 1 by omega)] using And.intro hxR hxQ
        · have hilast : i.val = m + 2 := by have := i.isLt; omega
          have hieq : i = Fin.last (m + 2) := Fin.ext hilast
          have hnext : (i + 1).val = 0 := by rw [hieq, Fin.last_add_one]; rfl
          have he0 := C.epsilon_eq 0 (hact 0 (Nat.zero_le _))
          have hx0 : Q.center ∈ (C.neck 0).carrier := by
            rw [hQcenter]
            apply (C.neck 0).coordinate_map_mem
            refine ⟨mem_univ _, ?_⟩
            rw [he0]
            change -L < -(17 * L / 20) ∧ -(17 * L / 20) < L
            constructor <;> linarith
          have hxQ : Q.center ∈ Q.carrier :=
            Q.central_sphere_subset Q.center_on_central_sphere
          refine ⟨Q.center, ?_⟩
          simpa only [W, hilast, hnext, if_neg (show ¬m + 2 ≤ m by omega),
            if_neg (show ¬m + 2 = m + 1 by omega), if_pos (Nat.zero_le m),
            Nat.cast_zero, mem_inter_iff] using And.intro hxQ hx0
  have hwholeK : (⋃ i : I, (K i).carrier) = univ := by
    apply Subset.antisymm (subset_univ _)
    rw [← hwhole]
    apply EpsilonNeck.subset_iUnion_carrier_of_retained_cover K a b ha hb hcover
      H.connected_X.isPreconnected
    refine ⟨(K 0).center, ?_, mem_iUnion.mpr ⟨0, ?_⟩⟩
    · rw [hwhole]; exact mem_univ _
    · exact (K 0).central_sphere_subset (K 0).center_on_central_sphere
  refine ⟨m + 2, K, a, b, fun i => Or.inl (hK i),
    fun i => (heK i).trans (heW i), ha, hb, hcover, hwholeK, ?_⟩
  intro i
  simpa only [hcarrier i, hcarrier (i + 1)] using hoverlap i

end PoincareConjecture
