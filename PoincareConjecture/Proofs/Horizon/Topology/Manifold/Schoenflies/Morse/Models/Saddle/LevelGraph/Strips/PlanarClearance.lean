import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.Projection
import PoincareConjecture.Proofs.Horizon.Topology.Connected.IntervalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.HeightCoordinates









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
local notation "IR2" => 𝓘(Real, Real × Real)




theorem exists_projected_strip_family_clearance
    {ι : Type*} [Finite ι]
    {g : S2 → E3} (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {v : E3} (hv : ‖v‖ = 1) {c : Real} (p : S2)
    (hp : inner Real v (g p) = c)
    (a b : ι → Real) (hab : ∀ i, a i ≤ b i)
    {w : Real} (hw : 0 < w) (F : ι → OpenPartialHomeomorph (Real × Real) S2)
    (hsource : ∀ i, (F i).source = Ioo (a i - w) (b i + w) ×ˢ Ioo (-w) w)
    (hF : ∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F i) (F i).source)
    (hheight : ∀ i z, z ∈ (F i).source → inner Real v (g (F i z)) = c + z.2)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (hpnot : ∀ i, p ∉ F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real))) :
    ∃ d : Real, 0 < d ∧ d < w ∧ ∃ U : ι → Set (Real ∙ v)ᗮ,
      (∀ i, IsOpen (U i) ∧
        (Real ∙ v)ᗮ.orthogonalProjectionOnto (g p) ∉ U i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      ∀ i, Icc (a i - d) (b i + d) ×ˢ Icc (-d) d ⊆ (F i).source ∧
        (fun z => (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (F i z))) ''
          (Icc (a i - d) (b i + d) ×ˢ Icc (-d) d) ⊆ U i := by
  let π : S2 → (Real ∙ v)ᗮ := fun q => (Real ∙ v)ᗮ.orthogonalProjectionOnto (g q)
  have hπinj : InjOn π {q | inner Real v (g q) = c} := by
    intro q hq z hz heq
    apply hg.isEmbedding.injective
    apply (Poincare.Geometry.Euclidean.heightCoordinates hv).symm.injective
    exact Prod.ext (hq.trans hz.symm) heq
  have hcentral (i : ι) : Icc (a i) (b i) ×ˢ ({0} : Set Real) ⊆ (F i).source := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    have ht0 : t = 0 := ht
    subst t
    rw [hsource i]
    constructor
    · constructor <;> linarith [hs.1, hs.2]
    · constructor <;> linarith
  have hcentralHeight (i : ι) (z : Real × Real)
      (hz : z ∈ Icc (a i) (b i) ×ˢ ({0} : Set Real)) :
      inner Real v (g (F i z)) = c := by
    rw [hheight i z (hcentral i hz)]
    have hz0 : z.2 = 0 := hz.2
    rw [hz0, add_zero]
  have hprojectedDisjoint : Pairwise (fun i j =>
      Disjoint ((fun z => π (F i z)) '' (Icc (a i) (b i) ×ˢ ({0} : Set Real)))
        ((fun z => π (F j z)) '' (Icc (a j) (b j) ×ˢ ({0} : Set Real)))) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro x ⟨y, hy, hxy⟩ ⟨z, hz, hxz⟩
    have heq : F i y = F j z :=
      hπinj (hcentralHeight i y hy) (hcentralHeight j z hz) (hxy.trans hxz.symm)
    exact disjoint_left.mp (hdisjoint hij) ((F i).map_source (hcentral i hy))
      (heq ▸ (F j).map_source (hcentral j hz))
  have hprojectedAvoid (i : ι) :
      (fun z => π (F i z)) '' (Icc (a i) (b i) ×ˢ ({0} : Set Real)) ⊆
        ({π p} : Set (Real ∙ v)ᗮ)ᶜ := by
    rintro x ⟨z, hz, rfl⟩ heq
    have heq' : F i z = p := hπinj (hcentralHeight i z hz) hp heq
    exact hpnot i ⟨z, hz, heq'⟩
  obtain ⟨d, hd, U, hU, hUdisjoint, hrect⟩ :=
    Poincare.Topology.exists_disjoint_closed_interval_rectangles
      (fun i z => π (F i z)) a b hab (fun i => (F i).source)
      (fun i => (F i).open_source)
      (fun i => (contMDiffOn_projected_strip hg v (F i) (hF i)).continuousOn)
      hcentral hprojectedDisjoint (fun _ => ({π p} : Set (Real ∙ v)ᗮ)ᶜ)
      (fun _ => isClosed_singleton.isOpen_compl) hprojectedAvoid
  refine ⟨min d (w / 2), lt_min hd (by linarith),
    (min_le_right _ _).trans_lt (by linarith), U, ?_, hUdisjoint, ?_⟩
  · intro i
    refine ⟨(hU i).1, ?_⟩
    intro hin
    exact (hU i).2.1 hin rfl
  · intro i
    have hsmall : Icc (a i - min d (w / 2)) (b i + min d (w / 2)) ×ˢ
        Icc (-min d (w / 2)) (min d (w / 2)) ⊆
        Icc (a i - d) (b i + d) ×ˢ Icc (-d) d := by
      intro z hz
      exact ⟨⟨by linarith [hz.1.1, min_le_left d (w / 2)],
        by linarith [hz.1.2, min_le_left d (w / 2)]⟩,
        ⟨by linarith [hz.2.1, min_le_left d (w / 2)],
        by linarith [hz.2.2, min_le_left d (w / 2)]⟩⟩
    exact ⟨hsmall.trans (hrect i).1, (image_mono hsmall).trans (hrect i).2⟩




theorem exists_planarly_separated_strip_restrictions
    {ι : Type*} [Finite ι]
    {g : S2 → E3} (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {v : E3} (hv : ‖v‖ = 1) {c : Real} (p : S2)
    (hp : inner Real v (g p) = c)
    (a b : ι → Real) (hab : ∀ i, a i ≤ b i)
    {w : Real} (hw : 0 < w) (F : ι → OpenPartialHomeomorph (Real × Real) S2)
    (hsource : ∀ i, (F i).source = Ioo (a i - w) (b i + w) ×ˢ Ioo (-w) w)
    (hF : ∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (F i).symm (F i).target)
    (hheight : ∀ i z, z ∈ (F i).source → inner Real v (g (F i z)) = c + z.2)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (hpnot : ∀ i, p ∉ F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real))) :
    ∃ (d : Real) (U : ι → Set (Real ∙ v)ᗮ)
        (G : ι → OpenPartialHomeomorph (Real × Real) S2),
      0 < d ∧ d < w ∧
      (∀ i, (G i).source = Ioo (a i - d) (b i + d) ×ˢ Ioo (-d) d) ∧
      (∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (G i) (G i).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (G i).symm (G i).target) ∧
      (∀ i z, G i z = F i z) ∧
      (∀ i z, z ∈ (G i).source → inner Real v (g (G i z)) = c + z.2) ∧
      (∀ i, IsOpen (U i) ∧
        (Real ∙ v)ᗮ.orthogonalProjectionOnto (g p) ∉ U i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Pairwise (fun i j => Disjoint (G i).target (G j).target) ∧
      ∀ i q, q ∈ (G i).target →
        (Real ∙ v)ᗮ.orthogonalProjectionOnto (g q) ∈ U i := by
  obtain ⟨d, hd, hdw, U, hU, hUdisjoint, hrect⟩ :=
    exists_projected_strip_family_clearance hg hv p hp a b hab hw F hsource
      hF hheight hdisjoint hpnot
  let B (i : ι) : Set (Real × Real) := Ioo (a i - d) (b i + d) ×ˢ Ioo (-d) d
  have hB (i : ι) : IsOpen (B i) := isOpen_Ioo.prod isOpen_Ioo
  have hBrect (i : ι) : B i ⊆ Icc (a i - d) (b i + d) ×ˢ Icc (-d) d :=
    prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  let G (i : ι) := (F i).restrOpen (B i) (hB i)
  have hGs (i : ι) : (G i).source = B i := by
    rw [(F i).restrOpen_source (B i) (hB i)]
    exact inter_eq_right.mpr ((hBrect i).trans (hrect i).1)
  have hGU (i : ι) (q : S2) (hq : q ∈ (G i).target) :
      (Real ∙ v)ᗮ.orthogonalProjectionOnto (g q) ∈ U i := by
    have hz : (G i).symm q ∈ B i := hGs i ▸ (G i).map_target hq
    have heq : F i ((G i).symm q) = q := (G i).right_inv hq
    have himg := (hrect i).2
      (mem_image_of_mem (fun z => (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (F i z)))
        (hBrect i hz))
    rwa [heq] at himg
  refine ⟨d, U, G, hd, hdw, hGs,
    (fun i => (hF i).mono inter_subset_left),
    (fun i => (hFi i).mono inter_subset_left), (fun _ _ => rfl),
    (fun i z hz => hheight i z hz.1), hU, hUdisjoint, ?_, hGU⟩
  intro i j hij
  apply disjoint_left.mpr
  intro q hqi hqj
  exact disjoint_left.mp (hUdisjoint hij) (hGU i q hqi) (hGU j q hqj)

end Poincare.Manifold.Schoenflies.SaddleLevel
