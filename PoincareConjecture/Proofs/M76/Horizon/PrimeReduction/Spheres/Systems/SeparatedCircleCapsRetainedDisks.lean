import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.MemberCircleCut
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import PoincareConjecture.Proofs.M76.Mathlib.CubeShellGeometry
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

private theorem square_ball_pair {r : ℝ} (hr : 0 < r) :
    IsFinitePLBallPair P2 (closedBall (0 : P2) r) (sphere (0 : P2) r) := by
  have h := CoordinateHalfBoxes.base_ballPair hr
  have heq : CoordinateHalfBoxes.base r = closedBall (0 : P2) r := by
    ext x
    simp only [CoordinateHalfBoxes.base, mem_prod, mem_Icc, mem_closedBall,
      dist_zero_right, Prod.norm_def, Real.norm_eq_abs, max_le_iff, abs_le]
  have hb := h.frontier_eq_of_finrank_eq rfl
  rw [heq, frontier_closedBall _ (ne_of_gt hr)] at hb
  rwa [heq, ← hb] at h

private theorem square_shell_finite (a : ℝ) :
    ∃ K : SimplicialComplex ℝ P2, K.faces.Finite ∧
      K.space = {x : P2 | ‖x‖ ∈ Icc a 1} := by
  classical
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    square_ball_pair (by norm_num : (0 : ℝ) < 1)
  let A : Fin 4 → P2 →ᵃ[ℝ] ℝ :=
    ![(ContinuousLinearMap.fst ℝ ℝ ℝ).toLinearMap.toAffineMap,
      -(ContinuousLinearMap.fst ℝ ℝ ℝ).toLinearMap.toAffineMap,
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toLinearMap.toAffineMap,
      -(ContinuousLinearMap.snd ℝ ℝ ℝ).toLinearMap.toAffineMap]
  choose J hJ hJs using fun i => K.exists_finite_affineSlab_complex hK (A i) a 1
  obtain ⟨L, hL, hLs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion J hJ
  refine ⟨L, hL, hLs.trans ?_⟩
  ext x
  have hn : ‖x‖ = max |x.1| |x.2| := rfl
  have hbound (i : Fin 4) : A i x ≤ ‖x‖ := by
    fin_cases i <;> change _ ≤ max |x.1| |x.2|
    · exact (le_abs_self _).trans (le_max_left _ _)
    · exact (neg_le_abs _).trans (le_max_left _ _)
    · exact (le_abs_self _).trans (le_max_right _ _)
    · exact (neg_le_abs _).trans (le_max_right _ _)
  have hmax : ∃ i, A i x = ‖x‖ := by
    rcases le_total |x.2| |x.1| with h | h
    · rw [hn, max_eq_left h]
      rcases le_total 0 x.1 with h0 | h0
      · exact ⟨0, (abs_of_nonneg h0).symm⟩
      · exact ⟨1, (abs_of_nonpos h0).symm⟩
    · rw [hn, max_eq_right h]
      rcases le_total 0 x.2 with h0 | h0
      · exact ⟨2, (abs_of_nonneg h0).symm⟩
      · exact ⟨3, (abs_of_nonpos h0).symm⟩
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    rw [hJs i, hKs] at hi
    exact ⟨hi.2.1.trans (hbound i), by simpa using hi.1⟩
  · intro hx
    obtain ⟨i, hi⟩ := hmax
    refine ⟨i, ?_⟩
    rw [hJs i, hKs]
    refine ⟨by simpa using hx.2, ?_⟩
    change A i x ∈ Icc a 1
    rwa [hi]

theorem exists_retained_disk_and_annulus
    {d r U : Set V3} (hd : IsFinitePLBallPair P2 d r)
    (hU : IsOpen U) (hrU : r ⊆ U) :
    ∃ (a : ℝ) (f : P2 → V3) (k q b : Set V3),
      0 < a ∧ a < 1 ∧
      FinitePiecewiseAffineOn f (closedBall (0 : P2) 1) ∧
      InjOn f (closedBall (0 : P2) 1) ∧
      f '' closedBall (0 : P2) 1 = d ∧ f '' sphere (0 : P2) 1 = r ∧
      k = f '' closedBall (0 : P2) a ∧ q = f '' sphere (0 : P2) a ∧
      b = f '' {x : P2 | ‖x‖ ∈ Icc a 1} ∧
      IsFinitePLBallPair P2 k q ∧ k ∪ b = d ∧ k ∩ b = q ∧
      Disjoint k r ∧ r ⊆ b ∧ b ⊆ U ∧
      ∃ H : {x : P2 | ‖x‖ ∈ Icc a 1} ≃ₜ b,
        H.IsFinitePL ∧ (∀ x, (H x : V3) = f x) := by
  classical
  obtain ⟨e, he, her⟩ := hd.exists_homeomorph (square_ball_pair (by norm_num : (0 : ℝ) < 1))
  obtain ⟨f, hf, hef⟩ := he.symm
  have hfi : InjOn f (closedBall (0 : P2) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (e.symm.injective
      (Subtype.ext ((hef ⟨x, hx⟩).trans (hxy.trans (hef ⟨y, hy⟩).symm))))
  have hfd : f '' closedBall (0 : P2) 1 = d := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hx⟩]
      exact (e.symm ⟨x, hx⟩).property
    · intro hy
      refine ⟨e ⟨y, hy⟩, (e ⟨y, hy⟩).property, ?_⟩
      rw [← hef, e.symm_apply_apply]
  have hfr : f '' sphere (0 : P2) 1 = r := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, sphere_subset_closedBall hx⟩]
      exact (her _).mpr (by simpa using hx)
    · intro hy
      refine ⟨e ⟨y, hd.1 hy⟩, (her _).mp hy, ?_⟩
      rw [← hef, e.symm_apply_apply]
  let C := closedBall (0 : P2) 1
  let v : C → V3 := fun x => f x
  have hvc : Continuous v := hf.continuousOn.domRestrict
  let : CompactSpace C := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let bad : Set C := v ⁻¹' Uᶜ
  have hbad : IsCompact bad := (hU.isClosed_compl.preimage hvc).isCompact
  have hlt (x : C) (hx : x ∈ bad) : ‖(x : P2)‖ < 1 := by
    have hle : ‖(x : P2)‖ ≤ 1 := by
      simpa only [C, mem_closedBall, dist_zero_right] using x.property
    apply lt_of_le_of_ne hle
    intro heq
    apply hx
    exact hrU (hfr.subset ⟨x, by simpa using heq, rfl⟩)
  have hex : ∃ c : ℝ, c < 1 ∧ ∀ x ∈ bad, ‖(x : P2)‖ ≤ c :=
    hbad.exists_forall_le' (α := OrderDual ℝ)
      (continuous_norm.comp continuous_subtype_val).continuousOn hlt
  obtain ⟨c, hc, hcb⟩ := hex
  obtain ⟨a, hca, ha⟩ := exists_between (max_lt (show c < 1 from hc) zero_lt_one)
  have ha0 : 0 < a := (le_max_right c 0).trans_lt hca
  have hac : c < a := (le_max_left c 0).trans_lt hca
  let k := f '' closedBall (0 : P2) a
  let q := f '' sphere (0 : P2) a
  let b := f '' {x : P2 | ‖x‖ ∈ Icc a 1}
  have hasub : closedBall (0 : P2) a ⊆ C := closedBall_subset_closedBall ha.le
  have hshell : {x : P2 | ‖x‖ ∈ Icc a 1} ⊆ C := fun x hx => by
    simpa [C] using hx.2
  have hkb : k ∪ b = d := by
    rw [← hfd, ← image_union]
    congr 1
    ext x
    simp only [mem_union, mem_closedBall, dist_zero_right, mem_ofPred_eq, mem_Icc]
    constructor
    · rintro (hx | hx)
      · exact hx.trans ha.le
      · exact hx.2
    · intro hx
      exact (le_total ‖x‖ a).imp id (fun h => ⟨h, hx⟩)
  have hkbi : k ∩ b = q := by
    rw [← image_inter_on (fun x hx y hy hxy => hfi (hshell hx) (hasub hy) hxy)]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_closedBall, mem_sphere, dist_zero_right,
      mem_ofPred_eq, mem_Icc]
    constructor
    · intro hx
      exact le_antisymm hx.1 hx.2.1
    · intro hx
      exact ⟨hx.le, hx.ge, hx ▸ ha.le⟩
  have hkr : Disjoint k r := by
    rw [← hfr, disjoint_left]
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hzx⟩
    have heq := hfi (sphere_subset_closedBall hz) (hasub hx) hzx
    subst z
    have hn : ‖x‖ = 1 := by simpa using hz
    have hn' : ‖x‖ ≤ a := by simpa using hx
    linarith
  have hrb : r ⊆ b := by
    rw [← hfr]
    apply image_mono
    intro x hx
    have hn : ‖x‖ = 1 := by simpa using hx
    exact ⟨hn ▸ ha.le, hn.le⟩
  have hbU : b ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra hnot
    have hb : (⟨x, hshell hx⟩ : C) ∈ bad := hnot
    have hh : ‖x‖ ≤ c := hcb _ hb
    exact (not_le_of_gt hac) (hx.1.trans hh)
  obtain ⟨J, hJ, hJs⟩ := square_shell_finite a
  have hfann : FinitePiecewiseAffineOn f {x : P2 | ‖x‖ ∈ Icc a 1} := by
    rw [← hJs]
    exact hf.restrict J hJ (hJs.subset.trans hshell)
  obtain ⟨H, hH, hHeq⟩ := hfann.exists_homeomorph_image (hfi.mono hshell)
  exact ⟨a, f, k, q, b, ha0, ha, hf, hfi, hfd, hfr, rfl, rfl, rfl,
    (square_ball_pair ha0).image_of_subset hf hasub hfi, hkb, hkbi, hkr, hrb, hbU,
    H, hH, hHeq⟩

theorem ChartwisePLSphere.exists_separated_retained_circle_disks
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) (d : Fin 2 → Set V3) {r : Set V3}
    (hd : ∀ i, IsFinitePLBallPair P2 (d i) r)
    (hwhole : d 0 ∪ d 1 = sphere (0 : V3) 1) (hinter : d 0 ∩ d 1 = r)
    {O : Set X} (hO : IsOpen O) (hrO : s.map '' r ⊆ O) :
    ∃ (a : Fin 2 → ℝ) (f : Fin 2 → P2 → V3)
      (k q b : Fin 2 → Set V3),
      (∀ i, 0 < a i ∧ a i < 1 ∧
        FinitePiecewiseAffineOn (f i) (closedBall (0 : P2) 1) ∧
        InjOn (f i) (closedBall (0 : P2) 1) ∧
        f i '' closedBall (0 : P2) 1 = d i ∧
        f i '' sphere (0 : P2) 1 = r ∧
        k i = f i '' closedBall (0 : P2) (a i) ∧
        q i = f i '' sphere (0 : P2) (a i) ∧
        b i = f i '' {x : P2 | ‖x‖ ∈ Icc (a i) 1} ∧
        IsFinitePLBallPair P2 (k i) (q i) ∧
        k i ∪ b i = d i ∧ k i ∩ b i = q i ∧
        Disjoint (k i) r ∧ r ⊆ b i ∧
        s.map '' b i ⊆ O ∧
        PolyhedralPLInCharts e s.map (k i) ∧
        PolyhedralPLInCharts e s.map (b i) ∧
        PolyhedralPLInCharts e (s.map ∘ f i) (closedBall (0 : P2) 1) ∧
        ∃ H : {x : P2 | ‖x‖ ∈ Icc (a i) 1} ≃ₜ b i,
          H.IsFinitePL ∧ (∀ x, (H x : V3) = f i x)) ∧
      Disjoint (k 0) (k 1) ∧ b 0 ∩ b 1 = r ∧
      Disjoint (s.map '' k 0) (s.map '' k 1) ∧
      (s.map '' b 0) ∩ (s.map '' b 1) = s.map '' r ∧
      (s.map '' k 0) ∪ (s.map '' b 0) ∪
        ((s.map '' k 1) ∪ (s.map '' b 1)) = S := by
  classical
  have hdS (i : Fin 2) : d i ⊆ sphere (0 : V3) 1 := by
    fin_cases i
    · exact subset_union_left.trans hwhole.subset
    · exact subset_union_right.trans hwhole.subset
  have hrS : r ⊆ sphere (0 : V3) 1 := (hd 0).1.trans (hdS 0)
  have hopen : IsOpen ((fun x : sphere (0 : V3) 1 => s.map x) ⁻¹' O) :=
    hO.preimage s.piecewiseAffine.continuousOn.domRestrict
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp hopen
  have hrU : r ⊆ U := by
    intro x hx
    exact (Set.ext_iff.mp hUeq ⟨x, hrS hx⟩).mpr (hrO ⟨x, hx, rfl⟩)
  choose a f k q b ha ha1 hf hfi hfd hfr hk hq hb hkp hkb hkbi hkr hrb hbU H hH hHeq
    using fun i => exists_retained_disk_and_annulus (hd i) hU hrU
  have hkd (i : Fin 2) : k i ⊆ d i := subset_union_left.trans (hkb i).subset
  have hbd (i : Fin 2) : b i ⊆ d i := subset_union_right.trans (hkb i).subset
  have hks (i : Fin 2) := (hkd i).trans (hdS i)
  have hbs (i : Fin 2) := (hbd i).trans (hdS i)
  have hsi : InjOn s.map (sphere (0 : V3) 1) := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x, hx⟩, s.map_eq ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hdis : Disjoint (k 0) (k 1) := by
    rw [disjoint_left]
    intro x hx hy
    exact (disjoint_left.mp (hkr 0)) hx (hinter.subset ⟨hkd 0 hx, hkd 1 hy⟩)
  have hbi : b 0 ∩ b 1 = r := by
    apply Subset.antisymm
    · exact fun x hx => hinter.subset ⟨hbd 0 hx.1, hbd 1 hx.2⟩
    · exact fun x hx => ⟨hrb 0 hx, hrb 1 hx⟩
  refine ⟨a, f, k, q, b, ?_, hdis, hbi, ?_, ?_, ?_⟩
  · intro i
    have hkPL : PolyhedralPLInCharts e s.map (k i) := by
      obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hkp i
      rw [← hKs]
      exact s.piecewiseAffine.restrict_finite K hK (hKs.subset.trans (hks i))
    have hbPL : PolyhedralPLInCharts e s.map (b i) := by
      obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := (hH i).symm
      rw [← hKs]
      exact s.piecewiseAffine.restrict_finite K hK (hKs.subset.trans (hbs i))
    have hcomp : PolyhedralPLInCharts e (s.map ∘ f i) (closedBall (0 : P2) 1) := by
      obtain ⟨K, hK, hKs, hKa⟩ := hf i
      rw [← hKs]
      exact s.piecewiseAffine.comp_finitePiecewiseAffineOn K hK
        ⟨K, hK, rfl, hKa⟩ (fun x hx => hdS i ((hfd i).subset ⟨x, hKs.subset hx, rfl⟩))
    refine ⟨ha i, ha1 i, hf i, hfi i, hfd i, hfr i, hk i, hq i, hb i,
      hkp i, hkb i, hkbi i, hkr i, hrb i, ?_, hkPL, hbPL, hcomp, H i, hH i, hHeq i⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (Set.ext_iff.mp hUeq ⟨x, hbs i hx⟩).mp (hbU i hx)
  · rw [disjoint_left]
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hzx⟩
    have hzx' := hsi (hks 1 hz) (hks 0 hx) hzx
    exact disjoint_left.mp hdis hx (hzx' ▸ hz)
  · rw [← image_inter_on (fun x hx y hy hxy => hsi (hbs 1 hx) (hbs 0 hy) hxy), hbi]
  · rw [← image_union, ← image_union, hkb 0, hkb 1, ← image_union, hwhole]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [s.map_eq ⟨x, hx⟩]
      exact (s.parametrization ⟨x, hx⟩).property
    · intro hy
      obtain ⟨x, hx⟩ := s.parametrization.surjective ⟨y, hy⟩
      exact ⟨x, x.property, (s.map_eq x).trans (congrArg Subtype.val hx)⟩

end PoincareConjecture.M76
