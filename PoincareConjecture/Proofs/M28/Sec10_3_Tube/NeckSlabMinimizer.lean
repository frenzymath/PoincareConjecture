import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckLevelShortening
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMinimizer
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Regions











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}


def neckTailRegion (N : EpsilonNeck g) : TopologicalSpace.Opens M :=
  ⟨N.region (-(2 : ℝ) * N.epsilon⁻¹ / 3) ((7 : ℝ) * N.epsilon⁻¹ / 8),
    N.region_open _ _⟩


def neckTailCompactSet (N : EpsilonNeck g) : Set M :=
  N.coordinate_map ''
    (univ ×ˢ Icc (-(5 : ℝ) * N.epsilon⁻¹ / 8) ((3 : ℝ) * N.epsilon⁻¹ / 4))



theorem neckTailCompactSet_compact_subset (N : EpsilonNeck g) :
    IsCompact (neckTailCompactSet N) ∧
      neckTailCompactSet N ⊆ (neckTailRegion N : Set M) := by
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  refine ⟨N.isCompact_coordinate_slab_intrinsic (by linarith) (by linarith), ?_⟩
  rintro x ⟨z, hz, rfl⟩
  have hzA : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  change N.coordinate_map z ∈ N.carrier ∧
    -(2 : ℝ) * N.epsilon⁻¹ / 3 < (N.coordinate_inverse (N.coordinate_map z)).2 ∧
    (N.coordinate_inverse (N.coordinate_map z)).2 < (7 : ℝ) * N.epsilon⁻¹ / 8
  rw [N.coordinate_inverse_coordinate_map_of_axial z hzA]
  exact ⟨N.coordinate_map_mem_of_axial z hzA,
    by linarith [hz.2.1], by linarith [hz.2.2]⟩



theorem mem_neckTailCompactSet_iff (N : EpsilonNeck g) {x : M}
    (hx : x ∈ N.carrier) :
    x ∈ neckTailCompactSet N ↔
      -(5 : ℝ) * N.epsilon⁻¹ / 8 ≤ (N.coordinate_inverse x).2 ∧
      (N.coordinate_inverse x).2 ≤ (3 : ℝ) * N.epsilon⁻¹ / 4 := by
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzA : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    rw [N.coordinate_inverse_coordinate_map_of_axial z hzA]
    exact hz.2
  · intro hheight
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hheight⟩,
      N.coordinate_map_coordinate_inverse hx⟩



theorem neck_tail_incoming_sphere (N : EpsilonNeck g) :
    IsCompact (N.coordinate_map ''
      (univ ×ˢ ({-(7 : ℝ) * N.epsilon⁻¹ / 12} : Set ℝ))) ∧
    (N.coordinate_map ''
      (univ ×ˢ ({-(7 : ℝ) * N.epsilon⁻¹ / 12} : Set ℝ))).Nonempty ∧
    N.coordinate_map '' (univ ×ˢ ({-(7 : ℝ) * N.epsilon⁻¹ / 12} : Set ℝ)) ⊆
      neckTailCompactSet N := by
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have ha : -(7 : ℝ) * N.epsilon⁻¹ / 12 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Icc_self] using N.isCompact_coordinate_slab_intrinsic ha.1 ha.2
  · exact ⟨N.coordinate_map ((N.coordinate_inverse N.center).1,
      -(7 : ℝ) * N.epsilon⁻¹ / 12),
      ⟨((N.coordinate_inverse N.center).1, -(7 : ℝ) * N.epsilon⁻¹ / 12),
        ⟨mem_univ _, rfl⟩, rfl⟩⟩
  · intro x hx
    obtain ⟨hxN, hxlevel⟩ := (mem_coordinate_sphere_iff N ha x).mp hx
    apply (mem_neckTailCompactSet_iff N hxN).mpr
    rw [hxlevel]
    constructor <;> linarith

private theorem tail_level_subset_region (N : EpsilonNeck g) {s : ℝ}
    (hs : s = -(7 : ℝ) * N.epsilon⁻¹ / 12 ∨ s = (5 : ℝ) * N.epsilon⁻¹ / 8) :
    s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧
    N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ)) ⊆ (neckTailRegion N : Set M) := by
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hsA : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    rcases hs with rfl | rfl <;> constructor <;> linarith
  refine ⟨hsA, ?_⟩
  intro x hx
  obtain ⟨hxN, hxlevel⟩ := (mem_coordinate_sphere_iff N hsA x).mp hx
  change x ∈ N.carrier ∧
    -(2 : ℝ) * N.epsilon⁻¹ / 3 < (N.coordinate_inverse x).2 ∧
    (N.coordinate_inverse x).2 < (7 : ℝ) * N.epsilon⁻¹ / 8
  refine ⟨hxN, ?_⟩
  rw [hxlevel]
  rcases hs with rfl | rfl <;> constructor <;> linarith

private theorem exists_tail_level_return (N : EpsilonNeck g)
    {γ : ℝ → M} (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγW : MapsTo γ (Icc (0 : ℝ) 1) (neckTailRegion N : Set M))
    (h0 : (N.coordinate_inverse (γ 0)).2 = -(7 : ℝ) * N.epsilon⁻¹ / 12)
    (h1 : |(N.coordinate_inverse (γ 1)).2| ≤ N.epsilon⁻¹ / 2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hexit : γ t ∉ neckTailCompactSet N) :
    ∃ s c d : ℝ,
      (s = -(7 : ℝ) * N.epsilon⁻¹ / 12 ∨ s = (5 : ℝ) * N.epsilon⁻¹ / 8) ∧
      0 ≤ c ∧ c ≤ t ∧ t ≤ d ∧ d ≤ 1 ∧
      γ c ∈ N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ)) ∧
      γ d ∈ N.coordinate_map '' (univ ×ˢ ({s} : Set ℝ)) ∧
      N.epsilon⁻¹ / 24 ≤
        |(N.coordinate_inverse (γ t)).2 - (N.coordinate_inverse (γ c)).2| := by
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hγN : MapsTo γ (Icc (0 : ℝ) 1) N.carrier := fun _ hu => (hγW hu).1
  let height : ℝ → ℝ := fun u => (N.coordinate_inverse (γ u)).2
  have hheight : ContinuousOn height (Icc (0 : ℝ) 1) :=
    (continuous_snd.comp_continuousOn N.coordinate_inverse_smooth.continuousOn).comp
      hγ hγN
  have hband : -(N.epsilon⁻¹ / 2) ≤ height 1 ∧ height 1 ≤ N.epsilon⁻¹ / 2 :=
    abs_le.mp h1
  have hout : height t < -(5 : ℝ) * N.epsilon⁻¹ / 8 ∨
      (3 : ℝ) * N.epsilon⁻¹ / 4 < height t := by
    have h := (mem_neckTailCompactSet_iff N (hγN ht)).not.mp hexit
    rcases lt_or_ge (height t) (-(5 : ℝ) * N.epsilon⁻¹ / 8) with hlo | hlo
    · exact Or.inl hlo
    · exact Or.inr (lt_of_not_ge (fun hhi => h ⟨hlo, hhi⟩))
  rcases hout with hlo | hhi
  · let s := -(7 : ℝ) * N.epsilon⁻¹ / 12
    have hs := (tail_level_subset_region N (s := s) (Or.inl rfl)).1
    obtain ⟨d, hd, hds⟩ := intermediate_value_Icc ht.2
      (hheight.mono (Icc_subset_Icc ht.1 le_rfl))
      (show s ∈ Icc (height t) (height 1) from ⟨by dsimp [s]; linarith,
        by dsimp [s]; linarith [hband.1]⟩)
    refine ⟨s, 0, d, Or.inl rfl, le_rfl, ht.1, hd.1, hd.2, ?_, ?_, ?_⟩
    · exact (mem_coordinate_sphere_iff N hs _).mpr ⟨hγN (by norm_num), h0⟩
    · exact (mem_coordinate_sphere_iff N hs _).mpr
        ⟨hγN ⟨ht.1.trans hd.1, hd.2⟩, hds⟩
    · change N.epsilon⁻¹ / 24 ≤ |height t - height 0|
      have hh0 : height 0 = -(7 : ℝ) * N.epsilon⁻¹ / 12 := h0
      linarith [neg_le_abs (height t - height 0)]
  · let s := (5 : ℝ) * N.epsilon⁻¹ / 8
    have hs := (tail_level_subset_region N (s := s) (Or.inr rfl)).1
    have hh0 : height 0 = -(7 : ℝ) * N.epsilon⁻¹ / 12 := h0
    obtain ⟨c, hc, hcs⟩ := intermediate_value_Icc ht.1
      (hheight.mono (Icc_subset_Icc le_rfl ht.2))
      (show s ∈ Icc (height 0) (height t) from ⟨by dsimp [s]; linarith,
        by dsimp [s]; linarith⟩)
    obtain ⟨d, hd, hds⟩ := intermediate_value_Icc' ht.2
      (hheight.mono (Icc_subset_Icc ht.1 le_rfl))
      (show s ∈ Icc (height 1) (height t) from ⟨by dsimp [s]; linarith [hband.2],
        by dsimp [s]; linarith⟩)
    refine ⟨s, c, d, Or.inr rfl, hc.1, hc.2, hd.1, hd.2, ?_, ?_, ?_⟩
    · exact (mem_coordinate_sphere_iff N hs _).mpr
        ⟨hγN ⟨hc.1, hc.2.trans ht.2⟩, hcs⟩
    · exact (mem_coordinate_sphere_iff N hs _).mpr
        ⟨hγN ⟨ht.1.trans hd.1, hd.2⟩, hds⟩
    · change N.epsilon⁻¹ / 24 ≤ |height t - height c|
      have hhcs : height c = (5 : ℝ) * N.epsilon⁻¹ / 8 := hcs
      linarith [le_abs_self (height t - height c)]





theorem exists_neck_tail_minimizer [T2Space M] [T3Space M]
    (N : EpsilonNeck g) (hε : N.epsilon ≤ neckLevelShorteningEpsilon)
    {w q : M}
    (hw : w ∈ N.coordinate_map ''
      (univ ×ˢ ({-(7 : ℝ) * N.epsilon⁻¹ / 12} : Set ℝ)))
    (hq : q ∈ N.carrier) (hheight : |(N.coordinate_inverse q).2| ≤ N.epsilon⁻¹ / 2) :
    ∃ γ : ℝ → M, γ 0 = w ∧ γ 1 = q ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
      MapsTo γ (Icc (0 : ℝ) 1) (neckTailRegion N : Set M) ∧
      g.pathELength γ 0 1 = intrinsicEDist g (neckTailRegion N : Set M) w q ∧
      g.pathELength γ 0 1 ≠ ⊤ := by
  let W := neckTailRegion N
  let K := neckTailCompactSet N
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  obtain ⟨hK, hKW⟩ := neckTailCompactSet_compact_subset N
  have hwK : w ∈ K := (neck_tail_incoming_sphere N).2.2 hw
  have hqK : q ∈ K := (mem_neckTailCompactSet_iff N hq).mpr
    ⟨by linarith [(abs_le.mp hheight).1], by linarith [(abs_le.mp hheight).2]⟩
  have hconnected : IsConnected (W : Set M) :=
    N.isConnected_region (by linarith) (by linarith) (by linarith)
  let : PreconnectedSpace W := Subtype.preconnectedSpace hconnected.2
  let d := intrinsicEDist g (W : Set M) w q
  have hdfinite : d ≠ ⊤ := by
    have h := (intrinsicOpenMetric g W).edist_ne_top
      (⟨w, hKW hwK⟩ : W) (⟨q, hKW hqK⟩ : W)
    rw [intrinsicOpenMetric_edist] at h
    exact h
  let delta := N.scale * N.epsilon⁻¹ / 96
  have hdelta : 0 < delta := div_pos (mul_pos N.scale_pos hA) (by norm_num)
  have hnear : d < ENNReal.ofReal (d.toReal + delta) := by
    apply (ENNReal.toReal_lt_toReal hdfinite ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    linarith only [hdelta]
  obtain ⟨α, hα0, hα1, hα, hαW, hαlen⟩ := exists_intrinsic_competitor g hnear
  obtain ⟨paths, hpaths, htendsto⟩ :=
    exists_intrinsic_minimizing_sequence_of_path g zero_le_one hα hαW hαlen
  rw [hα0, hα1] at htendsto
  have hpaths' (k : ℕ) : paths k 0 = w ∧ paths k 1 = q ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (paths k) (Icc (0 : ℝ) 1) ∧
      MapsTo (paths k) (Icc (0 : ℝ) 1) K ∧
      g.pathELength (paths k) 0 1 < ENNReal.ofReal (d.toReal + delta) := by
    obtain ⟨h0, h1, hsmooth, hW, hlength⟩ := hpaths k
    have hp : paths k 0 = w := h0.trans hα0
    have hq' : paths k 1 = q := h1.trans hα1
    refine ⟨hp, hq', hsmooth, ?_, hlength⟩
    intro t ht
    by_contra hnot
    have hstart : (N.coordinate_inverse (paths k 0)).2 =
        -(7 : ℝ) * N.epsilon⁻¹ / 12 := by
      rw [hp]
      exact ((mem_coordinate_sphere_iff N
        (tail_level_subset_region N (Or.inl rfl)).1 w).mp hw).2
    have hend : |(N.coordinate_inverse (paths k 1)).2| ≤ N.epsilon⁻¹ / 2 := by
      rw [hq']
      exact hheight
    obtain ⟨s, c, e, hs, hc, hct, hte, he, hcsphere, hesphere, hdisplacement⟩ :=
      exists_tail_level_return N hsmooth.continuousOn hW hstart hend ht hnot
    obtain ⟨hsA, hsW⟩ := tail_level_subset_region N hs
    obtain ⟨β, hβ0, hβ1, hβ, hβW, hshort⟩ :=
      exists_neck_level_excursion_replacement N hε hsA hsW hc hct hte he
        hsmooth hW hcsphere hesphere
        (fun _ hu => (hW ((Icc_subset_Icc hc (hte.trans he)) hu)).1) hdisplacement
    have hdβ : d ≤ g.pathELength β 0 1 := by
      simpa only [hβ0, hβ1, hp, hq'] using
        intrinsicEDist_le_pathELength g zero_le_one hβ hβW
    have hsave : d + ENNReal.ofReal delta ≤ g.pathELength (paths k) 0 1 :=
      (add_le_add hdβ le_rfl).trans hshort
    have hbound : g.pathELength (paths k) 0 1 < d + ENNReal.ofReal delta := by
      simpa only [ENNReal.ofReal_add ENNReal.toReal_nonneg hdelta.le,
        ENNReal.ofReal_toReal hdfinite] using hlength
    exact (not_lt_of_ge hsave) hbound
  exact exists_intrinsic_minimizer_of_compact_sequence g W hK hKW
    (fun k => (hpaths' k).2.2.1) (fun k => (hpaths' k).1)
    (fun k => (hpaths' k).2.1) (fun k => (hpaths' k).2.2.2.1)
    (fun k => (hpaths' k).2.2.2.2) htendsto

end PoincareConjecture.M28
