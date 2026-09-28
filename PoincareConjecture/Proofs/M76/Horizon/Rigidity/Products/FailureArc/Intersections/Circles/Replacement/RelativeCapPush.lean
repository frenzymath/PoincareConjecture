import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Replacement.LocalOppositeStrip
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Replacement.DiskCutoff
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.OriginalDiskBicollar

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : P2) 1
local notation "Rim" => sphere (0 : P2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (0 : ℝ) 1

theorem exists_original_relative_cap_push
    {X ι B : Type*} [MetricSpace X]
    [TopologicalSpace B] [CompactSpace B] [PreconnectedSpace B]
    {e : ι → OpenPartialHomeomorph X V3} {R S A T Z : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R)
    (j : P2 → X) (hj : PolyhedralPLInCharts e j D) (hji : InjOn j D)
    (hjS : MapsTo j D S) (hA : IsClosed A) (hT : IsClosed T) (hZ : IsClosed Z)
    (hja : Disjoint (j '' Rim) A) (hjZ : Disjoint (j '' D) Z)
    (hjT : ∀ x ∈ D, j x ∈ T ↔ x ∈ Rim)
    (p : B × J → X) (hp : Continuous p)
    (hp0 : ∀ b, p (b,⟨0,by norm_num⟩) ∈ j '' ball (0 : P2) 1)
    (hproper : ∀ z, p z ∈ S ↔ (z.2 : ℝ) = 0)
    (hcover : A ⊆ S ∪ range p ∪ Z) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k D ∧ InjOn k D ∧
      MapsTo k D (interior R) ∧ EqOn k j Rim ∧
      Disjoint (k '' D) A ∧ (∀ x ∈ D, k x ∈ T ↔ x ∈ Rim) := by
  classical
  obtain ⟨b,hb,hbi,hbR,hb0,hbS,_,hbint⟩ :=
    s.exists_original_disk_bicollar hR he hSR isOpen_univ (subset_univ S) j hj hji hjS
  let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let f : D × I → X := fun z => b ((z.1 : P2),(z.2 : ℝ))
  have hfc : Continuous f := hb.continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)) (fun z => ⟨z.1.property,z.2.property⟩)
  have hfi : Function.Injective f := by
    intro z w hzw
    have h := hbi ⟨z.1.property,z.2.property⟩ ⟨w.1.property,w.2.property⟩ hzw
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  let H := hfc.isClosedEmbedding hfi |>.isEmbedding.toHomeomorph
  have hK : range f = b '' (D ×ˢ I) := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨((z.1 : P2),(z.2 : ℝ)),⟨z.1.property,z.2.property⟩,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(⟨z.1,hz.1⟩,⟨z.2,hz.2⟩),rfl⟩
  have hzero (z : D × I) : (H z : X) ∈ S ↔ (z.2 : ℝ) = 0 :=
    hbS _ ⟨z.1.property,z.2.property⟩
  have hpO (q : B) : p (q,⟨0,by norm_num⟩) ∈ interior (range f) := by
    obtain ⟨x,hx,hxval⟩ := hp0 q
    rw [hK,hbint]
    refine ⟨(x,0),⟨hx,by norm_num⟩,?_⟩
    exact (hb0 x (ball_subset_closedBall hx)).trans hxval
  obtain ⟨δ,positive,hδ,hδhalf,havoid⟩ :=
    exists_local_opposite_strip_avoiding_surface H isOpen_interior interior_subset
      hzero p hp hpO hproper isCompact_univ hZ
      (fun x _ => Set.disjoint_left.mp hjZ
        ⟨x,x.property,(hb0 x x.property).symm⟩) hcover
  have hd : IsFinitePLBallPair P2 D Rim := by
    have h := CoordinateHalfBoxes.base_ballPair (show (0 : ℝ) < 1 by norm_num)
    have hbase : CoordinateHalfBoxes.base 1 = D := by
      ext x
      simp only [CoordinateHalfBoxes.base,mem_prod,mem_Icc,mem_closedBall,
        dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le]
    have hfront := h.frontier_eq_of_finrank_eq rfl
    rw [hbase,frontier_closedBall _ one_ne_zero] at hfront
    rwa [hbase,←hfront] at h
  let contact := D ∩ j ⁻¹' A
  have hcontact : IsCompact contact := hd.isCompact.of_isClosed_subset
    (hj.continuousOn.preimage_isClosed_of_isClosed hd.isCompact.isClosed hA) inter_subset_left
  have hcontactD : contact ⊆ D \ Rim := by
    intro x hx
    exact ⟨hx.1,fun hr => Set.disjoint_left.mp hja ⟨x,hr,rfl⟩ hx.2⟩
  obtain ⟨w,Q,hw,hQ,hQD,hCQ,hwbound,hwpos,hwzero⟩ :=
    exists_finitePL_disk_cutoff hd hcontact hcontactD (by norm_num : (0 : ℝ) < 1)
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let g : Q × I → X := fun z => b ((z.1 : P2),(z.2 : ℝ))
  have hg : Continuous g := hb.continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
    (fun z => ⟨(hQD z.1.property).1,z.2.property⟩)
  obtain ⟨r,hr,_,hthin⟩ := hg.exists_closed_strip_subset hT.isOpen_compl (by
    intro x
    change b ((x : P2),0) ∉ T
    rw [hb0 x (hQD x.property).1]
    exact fun h => (hQD x.property).2 ((hjT x (hQD x.property).1).mp h))
  let ε := min δ r
  have hε : 0 < ε := lt_min hδ hr
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεr : ε ≤ r := min_le_right _ _
  let v : P2 → ℝ := fun x => if positive then -(ε * w x) else ε * w x
  have hv : FinitePiecewiseAffineOn v D := by
    cases positive
    · exact (hw.postcomp (ε • ContinuousAffineMap.id ℝ ℝ)).congr (fun _ _ => rfl)
    · exact (hw.postcomp ((-ε) • ContinuousAffineMap.id ℝ ℝ)).congr
        (fun x _ => by simp [v])
  have hvabs (x : P2) (hx : x ∈ D) : |v x| ≤ ε := by
    have hwx := hwbound x hx
    have hmul : 0 ≤ ε * w x := mul_nonneg hε.le hwx.1
    have hle : ε * w x ≤ ε := by nlinarith [hwx.2]
    cases positive <;> simp only [v,Bool.false_eq_true,reduceIte,abs_neg,
      abs_of_nonneg hmul] <;> exact hle
  have hvI (x : P2) (hx : x ∈ D) : v x ∈ I := by
    have hh := abs_le.mp (hvabs x hx)
    constructor <;> linarith
  have hv0 (x : P2) (hx : x ∈ D \ Q) : v x = 0 := by
    simp only [v,hwzero x hx,mul_zero,neg_zero,ite_self]
  obtain ⟨L,hL,hLD,_⟩ := hw
  have hid : FinitePiecewiseAffineOn (id : P2 → P2) D :=
    ⟨L,hL,hLD,L.affineOnFaces_affine (ContinuousAffineMap.id ℝ P2)⟩
  have hgraph := hid.prod_mk hv
  let k : P2 → X := fun x => b (x,v x)
  have hk : PolyhedralPLInCharts e k D := by
    rw [←hLD]
    exact hb.comp_finitePiecewiseAffineOn L hL (hLD.symm ▸ hgraph)
      (fun x hx => ⟨hLD.subset hx,hvI x (hLD.subset hx)⟩)
  have hki : InjOn k D := by
    intro x hx y hy hxy
    exact congrArg Prod.fst (hbi ⟨hx,hvI x hx⟩ ⟨hy,hvI y hy⟩ hxy)
  have hkrim (x : P2) (hx : x ∈ Rim) : k x = j x := by
    have hxD := sphere_subset_closedBall hx
    change b (x,v x) = j x
    rw [hv0 x ⟨hxD,fun hq => (hQD hq).2 hx⟩,hb0 x hxD]
  refine ⟨k,hk,hki,fun x hx => (hbR ⟨hx,hvI x hx⟩).2,hkrim,?_,?_⟩
  · apply Set.disjoint_left.mpr
    rintro y ⟨x,hx,rfl⟩ hy
    by_cases hweight : w x = 0
    · have hvx : v x = 0 := by simp only [v,hweight,mul_zero,neg_zero,ite_self]
      have hjx : j x ∈ A := by simpa only [k,hvx,hb0 x hx] using hy
      exact (ne_of_gt (hwpos x ⟨hx,hjx⟩)) hweight
    · apply havoid ⟨x,hx⟩ (mem_univ _) ⟨v x,hvI x hx⟩ _ hy
      have hwp : 0 < w x := lt_of_le_of_ne (hwbound x hx).1 (Ne.symm hweight)
      have hm : 0 < ε * w x := mul_pos hε hwp
      have hmle : ε * w x ≤ δ := by nlinarith [(hwbound x hx).2]
      cases positive <;> simp only [v,Bool.false_eq_true,reduceIte]
      · exact ⟨hm,hmle⟩
      · exact ⟨by linarith,by linarith⟩
  · intro x hx
    constructor
    · intro hkt
      by_cases hxQ : x ∈ Q
      · exact False.elim (hthin ⟨x,hxQ⟩ ⟨v x,hvI x hx⟩
          ((hvabs x hx).trans hεr) hkt)
      · have hvx := hv0 x ⟨hx,hxQ⟩
        have hjx : j x ∈ T := by simpa only [k,hvx,hb0 x hx] using hkt
        exact (hjT x hx).mp hjx
    · intro hxR
      rw [hkrim x hxR]
      exact (hjT x hx).mpr hxR

end PoincareConjecture.M76.Dehn.Annuli
