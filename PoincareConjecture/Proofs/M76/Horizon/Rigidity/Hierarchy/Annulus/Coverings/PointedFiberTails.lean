import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.ThirdPhaseArcs
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.SourceAnnulusNormalDisplacement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.FiniteClosedPartition
import Mathlib.Topology.Order.IntermediateValue









set_option autoImplicit false
open Set Geometry Topology

namespace IsCoveringMap

private theorem range_subset_finite_arc_part
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {n : ℕ} (arc : Fin n → C(unitInterval, X))
    (hdis : Pairwise (fun i j => Disjoint (range (arc i)) (range (arc j))))
    (f : C(unitInterval, X)) (hf : range f ⊆ ⋃ i, range (arc i))
    (i : Fin n) (s : unitInterval) (hs : f s ∈ range (arc i)) :
    range f ⊆ range (arc i) := by
  let f' : C(unitInterval, (⋃ i, range (arc i))) :=
    ⟨fun t => ⟨f t, hf ⟨t, rfl⟩⟩, f.continuous.subtype_mk _⟩
  have hclopen := Poincare.Topology.isClopen_part_of_finite_closed_partition
    (fun i => range (arc i)) (fun i => (isCompact_range (arc i).continuous).isClosed) hdis i
  rintro _ ⟨t, rfl⟩
  exact hclopen.map_mem f'.continuous s hs t



theorem exists_fiber_parameter_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [CompactSpace X] [T2Space Y]
    {c : C(X, unitInterval × Y)} (hc : IsCoveringMap c) (theta : Y)
    {n : ℕ} (arc : Fin n → C(unitInterval, X))
    (hi : ∀ i, IsEmbedding (arc i))
    (hdis : Pairwise (fun i j => Disjoint (range (arc i)) (range (arc j))))
    (hwhole : (⋃ i, range (arc i)) = {x | (c x).2 = theta}) :
    ∀ i, ∃ H : unitInterval ≃ₜ unitInterval, ∀ t, H t = (c (arc i t)).1 := by
  obtain ⟨m, lift, _, hldis, hlwhole, hlcoord, _⟩ := hc.exists_finite_vertical_arc_family theta
  intro i
  have hstart : arc i 0 ∈ ⋃ k, range (lift k) := by
    rw [hlwhole, ← hwhole]
    exact mem_iUnion.mpr ⟨i, 0, rfl⟩
  obtain ⟨k, s, hs⟩ := mem_iUnion.mp hstart
  have hto : range (arc i) ⊆ range (lift k) :=
    range_subset_finite_arc_part lift hldis (arc i)
      (by rw [hlwhole, ← hwhole]; exact subset_iUnion (fun j => range (arc j)) i) k 0 ⟨s, hs⟩
  have hfrom : range (lift k) ⊆ range (arc i) :=
    range_subset_finite_arc_part arc hdis (lift k)
      (by rw [hwhole, ← hlwhole]; exact subset_iUnion (fun j => range (lift j)) k) i s ⟨0, hs.symm⟩
  let f : C(unitInterval, unitInterval) := ⟨fun t => (c (arc i t)).1, by fun_prop⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro t u htu
      obtain ⟨r, hr⟩ := hto ⟨t, rfl⟩
      obtain ⟨s, hs⟩ := hto ⟨u, rfl⟩
      have hrs : r = s := by
        change (c (arc i t)).1 = (c (arc i u)).1 at htu
        rw [← hr, ← hs, hlcoord, hlcoord] at htu
        exact htu
      exact (hi i).injective (hr.symm.trans (hrs ▸ hs))
    · intro t
      obtain ⟨s, hs⟩ := hfrom ⟨t, rfl⟩
      refine ⟨s, ?_⟩
      change (c (arc i s)).1 = t
      rw [hs, hlcoord]
  exact ⟨(Equiv.ofBijective f hbij).toHomeomorphOfContinuousClosed
    f.continuous f.continuous.isClosedMap, fun _ => rfl⟩

end IsCoveringMap

namespace PoincareConjecture.M76

open PLAnnularStrip

theorem interval_homeomorph_preimage_endpoint (H : unitInterval ≃ₜ unitInterval)
    (side : Bool) : H.symm (if side then 1 else 0) = 0 ∨ H.symm (if side then 1 else 0) = 1 := by
  have hmono := H.continuous.strictMono_of_inj H.injective
  rcases hmono with hmono | hanti
  · have h0 : H 0 = 0 := by
      apply le_antisymm
      · simpa using hmono.monotone (show (0 : unitInterval) ≤ H.symm 0 from bot_le)
      · exact bot_le
    have h1 : H 1 = 1 := by
      apply le_antisymm
      · exact le_top
      · simpa using hmono.monotone (show H.symm 1 ≤ (1 : unitInterval) from le_top)
    cases side
    · exact Or.inl (H.injective (by simpa using h0.symm))
    · exact Or.inr (H.injective (by simpa using h1.symm))
  · have h0 : H 0 = 1 := by
      apply le_antisymm
      · exact le_top
      · simpa using hanti.antitone (show (0 : unitInterval) ≤ H.symm 1 from bot_le)
    have h1 : H 1 = 0 := by
      apply le_antisymm
      · simpa using hanti.antitone (show H.symm 0 ≤ (1 : unitInterval) from le_top)
      · exact bot_le
    cases side
    · exact Or.inr (H.injective (by simpa using h1.symm))
    · exact Or.inl (H.injective (by simpa using h0.symm))

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Ann" => squareAnnulus 8 1



theorem exists_finitePL_marked_arc_tail
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    (j : ℝ × ℝ → X0) (arc : C(unitInterval, Ann))
    (hi : IsEmbedding arc) (param : ℝ → ℝ × ℝ)
    (hparam : ∀ t : unitInterval, param t = (arc t : ℝ × ℝ))
    (hPL : FinitePiecewiseAffineOn param (Icc (0 : ℝ) 1))
    (hsource : PolyhedralPLInCharts e (j ∘ param) (Icc (0 : ℝ) 1))
    (hmark : ∀ t, j (arc t) ∈ frontier R ↔ t = 0 ∨ t = 1)
    (s r : unitInterval) (hr : r = 0 ∨ r = 1) :
    ∃ (tail : C(unitInterval, Ann)) (q : ℝ → ℝ × ℝ),
      FinitePiecewiseAffineOn q (Icc (0 : ℝ) 1) ∧
      (∀ t : unitInterval, q t = (tail t : ℝ × ℝ)) ∧
      PolyhedralPLInCharts e (j ∘ q) (Icc (0 : ℝ) 1) ∧
      tail 0 = arc s ∧ tail 1 = arc r ∧
      range tail ⊆ range arc ∧ j (tail 1) ∈ frontier R ∧
      (s = r → ∀ t, tail t = arc s) ∧
      (s ≠ r → IsEmbedding tail) ∧
      (s ≠ r → ∀ t, j (tail t) ∈ frontier R → t = 0 ∨ t = 1) := by
  let f : ℝ →ᴬ[ℝ] ℝ := ((r : ℝ) - (s : ℝ)) • ContinuousAffineMap.id ℝ ℝ +
    ContinuousAffineMap.const ℝ ℝ (s : ℝ)
  have hf (t : ℝ) : f t = ((r : ℝ) - (s : ℝ)) * t + (s : ℝ) := rfl
  have hfrange : MapsTo f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    rw [hf]
    have h := (convex_Icc (0 : ℝ) 1) s.property r.property
      (sub_nonneg.mpr ht.2) ht.1 (show 1 - t + t = 1 by ring)
    simp only [smul_eq_mul] at h
    change 0 ≤ _ ∧ _ ≤ 1 at h ⊢
    constructor <;> nlinarith [h.1, h.2]
  let fI : C(unitInterval, unitInterval) :=
    ⟨fun t => ⟨f t, hfrange t.property⟩, by fun_prop⟩
  let tail := arc.comp fI
  let q := param ∘ f
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have hfPL : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1) :=
    ⟨K, hK, hKI, K.affineOnFaces_affine f⟩
  have hqPL : FinitePiecewiseAffineOn q (Icc (0 : ℝ) 1) := hPL.comp hfPL hfrange
  have hqsource : PolyhedralPLInCharts e (j ∘ q) (Icc (0 : ℝ) 1) := by
    have h := hsource.comp_finitePiecewiseAffineOn K hK (hKI.symm ▸ hfPL)
      (show MapsTo f K.space (Icc (0 : ℝ) 1) from hKI.symm ▸ hfrange)
    simpa only [hKI, q, Function.comp_def] using h
  have hf0 : fI 0 = s := by apply Subtype.ext; change f 0 = _; rw [hf]; ring
  have hf1 : fI 1 = r := by apply Subtype.ext; change f 1 = _; rw [hf]; ring
  refine ⟨tail, q, hqPL, fun t => hparam (fI t), hqsource,
    congrArg arc hf0, congrArg arc hf1, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨fI t, rfl⟩
  · change j (arc (fI 1)) ∈ frontier R
    rw [hf1]
    exact (hmark r).mpr hr
  · intro hsr t
    apply congrArg arc
    apply Subtype.ext
    change f t = (s : ℝ)
    rw [hf, hsr]
    ring
  · intro hsr
    apply hi.comp
    apply fI.continuous.isClosedEmbedding ?_ |>.isEmbedding
    intro t u htu
    have hh := congrArg Subtype.val htu
    change f t = f u at hh
    rw [hf, hf] at hh
    have hne : (r : ℝ) - (s : ℝ) ≠ 0 :=
      sub_ne_zero.mpr (fun h => hsr (Subtype.ext h.symm))
    exact Subtype.ext (mul_left_cancel₀ hne (by linarith))
  · intro hsr t ht
    have hh := (hmark (fI t)).mp ht
    have hsr' : (s : ℝ) ≠ (r : ℝ) := fun h => hsr (Subtype.ext h)
    have ht0 := t.property.1
    have ht1 := t.property.2
    have hs0 := s.property.1
    have hs1 := s.property.2
    rcases hr with hr | hr <;> rcases hh with hh | hh
    all_goals
      have hh' := congrArg Subtype.val hh
      change f t = _ at hh'
      rw [hf, hr] at hh'
      norm_num at hh'
    · right
      apply Subtype.ext
      change (t : ℝ) = 1
      have hs : (s : ℝ) ≠ 0 := by simpa [hr] using hsr'
      have hz : (s : ℝ) * (1 - (t : ℝ)) = 0 := by nlinarith
      have ht := (mul_eq_zero.mp hz).resolve_left hs
      linarith
    · left
      apply Subtype.ext
      change (t : ℝ) = 0
      nlinarith
    · left
      apply Subtype.ext
      change (t : ℝ) = 0
      nlinarith
    · right
      apply Subtype.ext
      change (t : ℝ) = 1
      have hs : (s : ℝ) ≠ 1 := by simpa [hr] using hsr'
      have hz : (1 - (s : ℝ)) * (1 - (t : ℝ)) = 0 := by nlinarith
      have ht := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hs.symm)
      linarith




theorem HamiltonZeroInstalledAnnulusPLArcFibers.exists_pointed_tail_family
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    {j : ℝ × ℝ → X0} {chi : C(H0, H0)} {c : C(Ann, unitInterval × C0)}
    (harcs : HamiltonZeroInstalledAnnulusPLArcFibers e R j chi c)
    (hc : IsCoveringMap c) (xi : C0) :
    ∃ (n : ℕ) (arc : Fin n → C(unitInterval, Ann))
      (param : Fin n → ℝ → ℝ × ℝ) (H : Fin n → unitInterval ≃ₜ unitInterval),
      (∀ i, IsEmbedding (arc i)) ∧
      (∀ i, FinitePiecewiseAffineOn (param i) (Icc (0 : ℝ) 1)) ∧
      (∀ i (t : unitInterval), param i t = (arc i t : ℝ × ℝ)) ∧
      (∀ i, PolyhedralPLInCharts e (j ∘ param i) (Icc (0 : ℝ) 1)) ∧
      Pairwise (fun i k => Disjoint (range (arc i)) (range (arc k))) ∧
      (⋃ i, range (arc i)) = {z | (c z).2 = xi} ∧
      (∀ i t, j (arc i t) ∈ frontier R ↔ t = 0 ∨ t = 1) ∧
      (∀ i t, H i t = (c (arc i t)).1) ∧
      (∀ i (s : unitInterval) (side : Bool),
        ∃ (tail : C(unitInterval, Ann)) (q : ℝ → ℝ × ℝ),
          FinitePiecewiseAffineOn q (Icc (0 : ℝ) 1) ∧
          (∀ t : unitInterval, q t = (tail t : ℝ × ℝ)) ∧
          PolyhedralPLInCharts e (j ∘ q) (Icc (0 : ℝ) 1) ∧
          tail 0 = arc i s ∧ c (tail 1) = (if side then 1 else 0, xi) ∧
          range tail ⊆ range (arc i) ∧ j (tail 1) ∈ frontier R ∧
          (∀ t, (c (tail t)).2 = xi) ∧
          ((c (arc i s)).1 = (if side then 1 else 0) → ∀ t, tail t = arc i s) ∧
          ((c (arc i s)).1 ≠ (if side then 1 else 0) → IsEmbedding tail) ∧
          ((c (arc i s)).1 ≠ (if side then 1 else 0) →
            ∀ t, j (tail t) ∈ frontier R → t = 0 ∨ t = 1)) ∧
      ∀ i k s t, c (arc i s) = c (arc k t) → arc i s ≠ arc k t → i ≠ k := by
  classical
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let : CompactSpace Ann := Dehn.annulusCylinderHomeomorph.compactSpace
  obtain ⟨n, arc, param, hi, hPL, hparam, hsource, hdis, hwhole, _, hmark⟩ := harcs xi
  have hhomes := hc.exists_fiber_parameter_homeomorph xi arc hi hdis hwhole
  choose H hH using hhomes
  have hphase (i : Fin n) (t : unitInterval) : (c (arc i t)).2 = xi :=
    hwhole.subset (mem_iUnion.mpr ⟨i, t, rfl⟩)
  refine ⟨n, arc, param, H, hi, hPL, hparam, hsource, hdis, hwhole, hmark, hH, ?_, ?_⟩
  · intro i s side
    let r := (H i).symm (if side then 1 else 0)
    have hr : r = 0 ∨ r = 1 := interval_homeomorph_preimage_endpoint (H i) side
    obtain ⟨tail, q, hq, hqt, hqsource, hzero, hone, hsub, hend, hconstant, hembed, hproper⟩ :=
      exists_finitePL_marked_arc_tail j (arc i) (hi i) (param i) (hparam i)
        (hPL i) (hsource i) (hmark i) s r hr
    have hrcoord : (c (arc i r)).1 = (if side then 1 else 0) := by
      rw [← hH]
      exact (H i).apply_symm_apply _
    have hne (h : (c (arc i s)).1 ≠ (if side then 1 else 0)) : s ≠ r := by
      intro hsr
      exact h (hsr ▸ hrcoord)
    refine ⟨tail, q, hq, hqt, hqsource, hzero, ?_, hsub, hend, ?_, ?_,
      fun h => hembed (hne h), fun h => hproper (hne h)⟩
    · rw [hone]
      exact Prod.ext hrcoord (hphase i r)
    · intro t
      obtain ⟨u, hu⟩ := hsub ⟨t, rfl⟩
      rw [← hu]
      exact hphase i u
    · intro hs
      apply hconstant
      apply (H i).injective
      rw [hH, hH, hs, hrcoord]
  · intro i k s t hsame hne hik
    subst k
    have hst : s = t := (H i).injective (by
      rw [hH, hH]
      exact congrArg Prod.fst hsame)
    exact hne (congrArg (arc i) hst)



structure HamiltonZeroPointedInteriorFiberTail
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3) (R : Set X0)
    (j : ℝ × ℝ → X0) (c : C(Ann, unitInterval × C0)) (x : Ann) (side : Bool)
    (tail : C(unitInterval, Ann)) (q : ℝ → ℝ × ℝ) : Prop where
  finitePL : FinitePiecewiseAffineOn q (Icc (0 : ℝ) 1)
  parameter : ∀ t : unitInterval, q t = (tail t : ℝ × ℝ)
  originalPL : PolyhedralPLInCharts e (j ∘ q) (Icc (0 : ℝ) 1)
  start : tail 0 = x
  endpoint : c (tail 1) = (if side then 1 else 0, (c x).2)
  embedding : IsEmbedding tail
  phase : ∀ t, (c (tail t)).2 = (c x).2
  proper : ∀ t, j (tail t) ∈ frontier R ↔ t = 1




theorem HamiltonZeroInstalledAnnulusPLArcFibers.exists_pointed_interior_tails
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    {j : ℝ × ℝ → X0} {chi : C(H0, H0)} {c : C(Ann, unitInterval × C0)}
    (harcs : HamiltonZeroInstalledAnnulusPLArcFibers e R j chi c)
    (hc : IsCoveringMap c) (x : Bool → Ann)
    (hnot : ∀ s, j (x s) ∉ frontier R) (hsame : c (x false) = c (x true))
    (side : Bool → Bool) :
    ∃ (tail : Bool → C(unitInterval, Ann)) (q : Bool → ℝ → ℝ × ℝ),
      (∀ s, HamiltonZeroPointedInteriorFiberTail e R j c (x s) (side s) (tail s) (q s)) ∧
      (x false ≠ x true → Disjoint (range (tail false)) (range (tail true))) := by
  classical
  let xi := (c (x false)).2
  obtain ⟨n, arc, _, _, _, _, _, _, hdis, hwhole, _, _, htail, hdifferent⟩ :=
    harcs.exists_pointed_tail_family hc xi
  have hxi (s : Bool) : (c (x s)).2 = xi := by
    cases s
    · rfl
    · exact congrArg Prod.snd hsame.symm
  have hpoints (s : Bool) : ∃ i t, arc i t = x s := by
    obtain ⟨i, t, ht⟩ := mem_iUnion.mp (hwhole.symm.subset (hxi s))
    exact ⟨i, t, ht⟩
  choose idx start hstart using hpoints
  have hex (s : Bool) : ∃ (tail : C(unitInterval, Ann)) (q : ℝ → ℝ × ℝ),
      HamiltonZeroPointedInteriorFiberTail e R j c (x s) (side s) tail q ∧
      range tail ⊆ range (arc (idx s)) := by
    obtain ⟨tail, q, hq, hqt, hqsource, hzero, hendcoord, hsub, hend,
        hphase, hconstant, hembed, hproper⟩ := htail (idx s) (start s) (side s)
    rw [hstart] at hzero hconstant hembed hproper
    have hne : (c (x s)).1 ≠ (if side s then 1 else 0) := by
      intro heq
      have h := hconstant heq 1
      rw [h] at hend
      exact hnot s hend
    refine ⟨tail, q, ⟨hq, hqt, hqsource, hzero, ?_, hembed hne, ?_, ?_⟩, hsub⟩
    · rw [hxi]
      exact hendcoord
    · intro t
      exact (hphase t).trans (hxi s).symm
    · intro t
      constructor
      · intro ht
        rcases hproper hne t ht with ht0 | ht1
        · rw [ht0, hzero] at ht
          exact (hnot s ht).elim
        · exact ht1
      · rintro rfl
        exact hend
  choose tail q hdata hsub using hex
  refine ⟨tail, q, hdata, ?_⟩
  intro hne
  have hi : idx false ≠ idx true := hdifferent (idx false) (idx true)
    (start false) (start true) (by rw [hstart, hstart]; exact hsame)
    (by rw [hstart, hstart]; exact hne)
  exact (hdis hi).mono (hsub false) (hsub true)

theorem HamiltonZeroInstalledAnnulusPLArcFibers.exists_pointed_interior_tail
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    {j : ℝ × ℝ → X0} {chi : C(H0, H0)} {c : C(Ann, unitInterval × C0)}
    (harcs : HamiltonZeroInstalledAnnulusPLArcFibers e R j chi c)
    (hc : IsCoveringMap c) (x : Ann) (hnot : j x ∉ frontier R) (side : Bool) :
    ∃ (tail : C(unitInterval, Ann)) (q : ℝ → ℝ × ℝ),
      HamiltonZeroPointedInteriorFiberTail e R j c x side tail q := by
  obtain ⟨tail, q, hdata, _⟩ := harcs.exists_pointed_interior_tails hc (fun _ => x)
    (fun _ => hnot) rfl (fun _ => side)
  exact ⟨tail false, q false, hdata false⟩

end PoincareConjecture.M76
