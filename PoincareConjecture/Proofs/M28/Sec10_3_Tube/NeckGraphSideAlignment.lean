import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckGraphSides
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckSignedRegions











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}




theorem neck_graph_side_alignment (N N' : EpsilonNeck g)
    {sigma lo a hi : ℝ} (hsigma : sigma = 1 ∨ sigma = -1)
    (hlo : -N.epsilon⁻¹ ≤ lo) (hhi : hi ≤ N.epsilon⁻¹)
    (hla : lo < a) (hah : a < hi)
    {f : UnitTwoSphere → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hdom : ∀ p, f p ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hrange : range (fun p : UnitTwoSphere => N.coordinate_map (p, sigma * a)) =
      range (fun p : UnitTwoSphere => N'.coordinate_map (p, f p)))
    (hcapture : neckSignedRegion N sigma lo hi ⊆ N'.carrier)
    (hclose : N'.center ∈ closure (neckSignedRegion N sigma a hi))
    (hcenter_out : N'.center ∉ N.carrier) :
    ∃ kappa : ℝ, (kappa = 1 ∨ kappa = -1) ∧
      0 < kappa * neckGraphHeight N' f N'.center ∧
      ∀ x ∈ neckSignedRegion N sigma lo hi,
        (0 < kappa * neckGraphHeight N' f x ↔ a < sigma * (N.coordinate_inverse x).2) ∧
        (kappa * neckGraphHeight N' f x < 0 ↔ sigma * (N.coordinate_inverse x).2 < a) := by
  let T := neckSignedRegion N sigma lo hi
  let O := neckSignedRegion N sigma a hi
  let I := neckSignedRegion N sigma lo a
  have ha : sigma * a ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    rcases hsigma with rfl | rfl
    · change -N.epsilon⁻¹ < 1 * a ∧ 1 * a < N.epsilon⁻¹
      simpa only [one_mul] using And.intro (hlo.trans_lt hla) (hah.trans_le hhi)
    · constructor <;> nlinarith
  have hOT : O ⊆ T := fun x hx => ⟨hx.1, hla.trans hx.2.1, hx.2.2⟩
  have hIT : I ⊆ T := fun x hx => ⟨hx.1, hx.2.1, hx.2.2.trans hah⟩
  have hzero (x : M) (hx : x ∈ T) :
      neckGraphHeight N' f x = 0 ↔ sigma * (N.coordinate_inverse x).2 = a := by
    have h := neckGraphHeight_eq_zero_iff N' hdom (hcapture hx)
    rw [← hrange] at h
    exact h.trans (mem_neck_slice_iff_signed_axis N hsigma ha hx.1)
  have hpN : N'.center ∈ N'.carrier :=
    N'.central_sphere_subset N'.center_on_central_sphere
  have hpne : neckGraphHeight N' f N'.center ≠ 0 := by
    intro hz
    have hmem := (neckGraphHeight_eq_zero_iff N' hdom hpN).mp hz
    rw [← hrange] at hmem
    obtain ⟨p, hp⟩ := hmem
    exact hcenter_out (hp ▸ N.coordinate_map_mem ⟨mem_univ _, ha⟩)
  obtain ⟨kappa, hkappa, hp⟩ : ∃ kappa : ℝ, (kappa = 1 ∨ kappa = -1) ∧
      0 < kappa * neckGraphHeight N' f N'.center := by
    rcases lt_or_gt_of_ne hpne with hn | hp
    · exact ⟨-1, Or.inr rfl, by nlinarith⟩
    · exact ⟨1, Or.inl rfl, by simpa only [one_mul] using hp⟩
  let F : M → ℝ := fun x => kappa * neckGraphHeight N' f x
  have hkne : kappa ≠ 0 := by rcases hkappa with rfl | rfl <;> norm_num
  have hF : ContinuousOn F N'.carrier :=
    continuousOn_const.mul (continuousOn_neckGraphHeight N' hf)
  have hOconn : IsPreconnected O :=
    isPreconnected_neckSignedRegion N hsigma (hlo.trans hla.le) hhi
  have hIconn : IsPreconnected I :=
    isPreconnected_neckSignedRegion N hsigma hlo (hah.le.trans hhi)
  have hOne (x : M) (hx : x ∈ O) : F x ≠ 0 := by
    intro hz
    have hq : neckGraphHeight N' f x = 0 := (mul_eq_zero.mp hz).resolve_left hkne
    exact (ne_of_gt hx.2.1) ((hzero x (hOT hx)).mp hq)
  have hIne (x : M) (hx : x ∈ I) : F x ≠ 0 := by
    intro hz
    have hq : neckGraphHeight N' f x = 0 := (mul_eq_zero.mp hz).resolve_left hkne
    exact (ne_of_lt hx.2.2) ((hzero x (hIT hx)).mp hq)
  have hPopen : IsOpen (N'.carrier ∩ F ⁻¹' Ioi 0) :=
    hF.isOpen_inter_preimage N'.carrier_open isOpen_Ioi
  obtain ⟨y, hyP, hyO⟩ := mem_closure_iff.mp hclose
    (N'.carrier ∩ F ⁻¹' Ioi 0) hPopen ⟨hpN, hp⟩
  have hpositive (x : M) (hx : x ∈ O) : 0 < F x :=
    hOconn.lt_of_ne (hF.mono (hOT.trans hcapture)) hOne ⟨y, hyO, hyP.2⟩ hx
  let p0 : UnitTwoSphere := (N.coordinate_inverse N.center).1
  let z0 : M := N.coordinate_map (p0, sigma * a)
  have hzN : z0 ∈ N.carrier := N.coordinate_map_mem ⟨mem_univ _, ha⟩
  have hzaxis : sigma * (N.coordinate_inverse z0).2 = a :=
    (mem_neck_slice_iff_signed_axis N hsigma ha hzN).mp ⟨p0, rfl⟩
  have hzT : z0 ∈ T := ⟨hzN, by rw [hzaxis]; exact hla, by rw [hzaxis]; exact hah⟩
  have hzGraph : z0 ∈ range (fun p : UnitTwoSphere => N'.coordinate_map (p, f p)) := by
    rw [← hrange]
    exact ⟨p0, rfl⟩
  obtain ⟨theta, htheta⟩ := hzGraph
  change N'.coordinate_map (theta, f theta) = z0 at htheta
  have hthetaT : N'.coordinate_map (theta, f theta) ∈ T := htheta.symm ▸ hzT
  obtain ⟨y, hyT, _, hyneg⟩ := exists_neckGraphHeight_negative_in_open N' f
    (isOpen_neckSignedRegion N sigma lo hi) theta hthetaT
    (hdom theta) hkappa
  have hya : sigma * (N.coordinate_inverse y).2 < a := by
    rcases lt_trichotomy (sigma * (N.coordinate_inverse y).2) a with h | h | h
    · exact h
    · have hq : neckGraphHeight N' f y = 0 := (hzero y hyT).mpr h
      rw [hq, mul_zero] at hyneg
      exact (lt_irrefl (0 : ℝ) hyneg).elim
    · have hpos := hpositive y ⟨hyT.1, h, hyT.2.2⟩
      exact ((not_lt_of_ge hyneg.le) hpos).elim
  have hnegative (x : M) (hx : x ∈ I) : F x < 0 :=
    hIconn.gt_of_ne (hF.mono (hIT.trans hcapture)) hIne
      ⟨y, ⟨hyT.1, hyT.2.1, hya⟩, hyneg⟩ hx
  refine ⟨kappa, hkappa, hp, ?_⟩
  intro x hx
  change (0 < F x ↔ a < sigma * (N.coordinate_inverse x).2) ∧
    (F x < 0 ↔ sigma * (N.coordinate_inverse x).2 < a)
  rcases lt_trichotomy (sigma * (N.coordinate_inverse x).2) a with h | h | h
  · have hn := hnegative x ⟨hx.1, hx.2.1, h⟩
    exact ⟨iff_of_false (not_lt_of_ge hn.le) (not_lt_of_ge h.le), iff_of_true hn h⟩
  · have hz : F x = 0 := by
      change kappa * neckGraphHeight N' f x = 0
      rw [(hzero x hx).mpr h, mul_zero]
    simp only [hz, h, lt_self_iff_false, iff_self, and_self]
  · have hp := hpositive x ⟨hx.1, h, hx.2.2⟩
    exact ⟨iff_of_true hp h, iff_of_false (not_lt_of_ge hp.le) (not_lt_of_ge h.le)⟩

end PoincareConjecture.M28
