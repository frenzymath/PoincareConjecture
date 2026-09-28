import PoincareConjecture.Proofs.M76.Wall.OriginalArcBallModel
import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryExteriorBallPair
import PoincareConjecture.Proofs.M76.Wall.OriginalBinaryExteriorDomains
import PoincareConjecture.Proofs.M76.Wall.OriginalEndpointFoot
import PoincareConjecture.Proofs.M76.Wall.OriginalSphereGraphModel
import PoincareConjecture.Proofs.M76.Wall.OriginalTwoFootSphereImage
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex TriangularRoofModel

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem PLDomain.exists_two_sphere_arc_attachment
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L : Set X}
    (he : PLDomain e L) (hL : IsCompact L)
    {q : ℝ → X} (hq : PolyhedralPLInCharts e q I) (hqi : InjOn q I)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∉ L)
    (S : Fin 2 → Set X) (hsphere : ∀ i, ChartwisePLSphere e (S i))
    (hSL : ∀ i, S i ⊆ frontier L)
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (hzero : q 0 ∈ S 0) (hone : q 1 ∈ S 1)
    {B W : Set X} (hfront : frontier L = B ∪ (S 0 ∪ S 1))
    (hBS : ∀ i, Disjoint B (S i)) (hW : IsOpen W) (hqW : MapsTo q I W)
    (hBW : Disjoint B W) (hout : ∀ i, (S i \ W).Nonempty)
    (U : Fin 2 → Set X) (hU : ∀ i, IsOpen (U i))
    (hU0 : q 0 ∈ U 0) (hU1 : q 1 ∈ U 1)
    (hUS : ∀ i, U i ∩ frontier L ⊆ S i) :
    ∃ R Snew : Set X, IsCompact R ∧ IsConnected R ∧ R ⊆ W ∧
      PLDomain e R ∧ PLDomain e (L ∪ R) ∧
      Nonempty (ChartwisePLSphere e Snew) ∧
      frontier (L ∪ R) = B ∪ Snew ∧ Disjoint B Snew ∧ (L ∩ R).Nonempty := by
  classical
  obtain ⟨s, F, C, K, A, H, g, N, Hext, v, n, p, hN, hD, hmodel⟩ :=
    he.exists_arc_ball_model hL hq hqi (hSL 0 hzero) (hSL 1 hone)
      hproper hW hqW U hU hU0 hU1 S hsphere hSL
  let E := s → ℝ × V3
  have hstarEq (d : DecidableEq E) (z : E) :
      @closedStar ℝ E _ _ _ _ d K z =
        @closedStar ℝ E _ _ _ _ (Classical.decEq E) K z := by
    cases Subsingleton.elim d (Classical.decEq E)
    rfl
  let : Fintype N.faces := hN.fintype
  let : Fintype (A 1).faces := hD.fintype
  obtain ⟨hC, hcore, hFc, hFPL, hK, hA, hKs, hA0, hA1, hA2, _, _,
    hHF, hgc, hg, hgPL, hNK, hNs, hDN, hAN, _, _, _, _, _, _, _,
    hdim, hstars, hpi, hp0, hp1, hedge, hcover, hverts, hcontact,
    hdisks, hchain, _, _, _⟩ := hmodel
  let : Fintype K.faces := hK.fintype
  have hLC : L ⊆ C := fun _ hx => interior_subset (hcore (Or.inl hx))
  have hSiC (i : Fin 2) : S i ⊆ C := (hSL i).trans (he.closed.frontier_subset.trans hLC)
  have hBC : B ⊆ C := fun _ hx =>
    hLC (he.closed.frontier_subset (hfront.symm.subset (Or.inl hx)))
  have hFi : InjOn F C := by
    intro x hx y hy hxy
    have heq : H ⟨x, hx⟩ = H ⟨y, hy⟩ := Subtype.ext
      ((hHF ⟨x, hx⟩).trans (hxy.trans (hHF ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective heq)
  let gx : E → X := fun z => g z
  have hgF (x : X) (hx : x ∈ C) : gx (F x) = x := by
    have heq := hg (H ⟨x, hx⟩)
    rw [H.symm_apply_apply] at heq
    simpa only [hHF] using heq
  have hFg (z : E) (hz : z ∈ K.space) : F (gx z) = z := by
    calc
      F (gx z) = F (H.symm ⟨z, hz⟩) := congrArg F (hg ⟨z, hz⟩)
      _ = (H (H.symm ⟨z, hz⟩) : E) := (hHF (H.symm ⟨z, hz⟩)).symm
      _ = z := by rw [H.apply_symm_apply]
  have hgi : InjOn gx K.space := by
    intro z hz w hw hzw
    exact (hFg z hz).symm.trans ((congrArg F hzw).trans (hFg w hw))
  obtain ⟨h, c, _, hh, hvalues, _, _, _, hcPL, hci, _, _, _, hmarks,
    _, _, hball, hfeet, hrims⟩ :=
    K.exists_binary_exterior_ball_pair N (A 2) (A 1) hNK hAN hDN
      (fun t ht => (hA 2).2.2 t (hNK ht))
      (fun t ht => (hA 1).2.2 t (hNK ht)) hdim p hpi hverts hedge hcover hcontact hchain
  let body : Set E := N.space ∩ {z | (1 / 2 : ℝ) ≤ h z}
  let level : Set E := N.space ∩ {z | h z = (1 / 2 : ℝ)}
  let R : Set X := gx '' body
  have hstars' : ∀ z ∈ (A 2).vertices,
      ∃ G : OpenPartialHomeomorph X V3,
        MapsTo (fun y => (g y : X)) (K.closedStar z).space G.source ∧
        (K.closedStar z).AffineOnFaces (fun y => G (g y)) ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        G.source ⊆ interior C ∩ W ∧
        (G.source ⊆ Lᶜ ∨ ∃ (ell : V3 →L[ℝ] ℝ) (w : V3), ell w = 1 ∧
          (∀ y ∈ G.source, y ∈ L ↔ 0 ≤ ell (G y)) ∧
          ∀ y ∈ G.source, y ∈ frontier L ↔ ell (G y) = 0) := by
    intro z hz
    obtain ⟨G, hsource, haff, hcompat, hinside, hbranch⟩ := hstars z hz
    refine ⟨G, hsource, haff, hcompat, hinside, ?_⟩
    rcases hbranch with haway | ⟨i, ell, w, _, hw, hhalf, hfr⟩
    · exact Or.inl haway
    · exact Or.inr ⟨ell, w, hw, hhalf, hfr⟩
  obtain ⟨hRc, hRW, hRPL, hUnionPL, _, hfrontUnion⟩ :=
    he.original_binary_exterior_domains (W := W) hLC K N (A 1) hK hNK (hA 1).1
      H g hgc hg F hFc hHF hNs hA1 (A 2).vertices hh hvalues
      (by simpa only [hstarEq] using hstars')
  let ep : Fin 2 → Fin (n + 2) := Fin.cases 0 (fun _ => Fin.last (n + 1))
  let endpoint : Fin 2 → X := Fin.cases (q 0) (fun _ => q 1)
  have hep (i : Fin 2) : p (ep i) = F (endpoint i) := by
    fin_cases i
    · exact hp0
    · exact hp1
  have hend (i : Fin 2) : endpoint i ∈ S i := by
    fin_cases i
    · exact hzero
    · exact hone
  have hpA (i : Fin 2) : p (ep i) ∈ (A 2).vertices :=
    hverts.symm.subset ⟨ep i, rfl⟩
  have hfinite : ((A 2).space ∩ (A 1).space).Finite := by
    rw [hcontact]
    exact (finite_singleton _).insert _
  have hpD (i : Fin 2) : p (ep i) ∈ (A 1).vertices := by
    have hpDs : p (ep i) ∈ (A 1).space := by
      rw [hep]
      exact hA1.symm.subset ⟨endpoint i, hSL i (hend i), rfl⟩
    exact (mem_vertices_of_finite_subcomplex_intersection (hA 2).1 (hA 1).1 hfinite
      ((A 2).vertices_subset_space (hpA i)) hpDs).2
  let foot (i : Fin 2) : Set E := c '' ((A 1).barycentricDualBlock {p (ep i)}).space
  let rim (i : Fin 2) : Set E := c ''
    (((N.barycentricDualBlock {p (ep i)}).link (p (ep i))).space ∩
      ((A 1).barycentricDualBlock {p (ep i)}).space)
  let sphere (i : Fin 2) : Set E := F '' S i
  have hfootS (i : Fin 2) : foot i ⊆ sphere i := by
    apply (original_endpoint_foot_subset_sphere he.closed hLC K (A 1) (hA 1).1
      H g hg F hHF hA1 U S hUS hdisjoint (hSL i (hend i)) (hend i)
      (hpD i) (hep i) ?_ hmarks).1
    obtain ⟨G, hsource, _, _, _, hbranch⟩ := hstars _ (hpA i)
    refine ⟨G, ?_, ?_⟩
    · simpa only [hstarEq] using hsource
    · rcases hbranch with haway | ⟨j, ell, w, hGU, _, _, _⟩
      · exact Or.inl haway
      · exact Or.inr ⟨j, hGU⟩
  have hdisk (i : Fin 2) : IsFinitePLBallPair (ℝ × ℝ) (foot i) (rim i) := by
    apply (hdisks _ (hpA i) (hpD i)).2.image_of_subset hcPL ?_ hci
    intro z hz
    apply space_subset_of_le (hA 1).1
    exact (A 1).barycentricSubdivision_isSubdivision.space_eq.subset
      (space_subset_of_le ((A 1).barycentricDualBlock_le {p (ep i)}) hz)
  have hrim (i : Fin 2) : rim i = foot i ∩ {z | h z = (1 / 2 : ℝ)} :=
    hrims _ (hpA i) (hpD i)
  have hfeet' : foot 0 ∪ foot 1 = (A 1).space ∩ {z | (1 / 2 : ℝ) ≤ h z} := hfeet
  have hSmark (i : Fin 2) : sphere i ⊆ (A 1).space :=
    (image_mono (hSL i)).trans hA1.symm.subset
  have hSdisj : Disjoint (sphere 0) (sphere 1) := by
    apply disjoint_left.mpr
    rintro z ⟨x, hx, hFx⟩ ⟨y, hy, hFy⟩
    have hxy := hFi (hSiC 0 hx) (hSiC 1 hy) (hFx.trans hFy.symm)
    subst y
    exact disjoint_left.mp (hdisjoint (by decide : (0 : Fin 2) ≠ 1)) hx hy
  have hfootBody (i : Fin 2) : foot i ⊆ body := by
    intro z hz
    have hzD : z ∈ (A 1).space ∩ {z | (1 / 2 : ℝ) ≤ h z} := by
      apply hfeet'.subset
      fin_cases i
      · exact Or.inl hz
      · exact Or.inr hz
    exact ⟨space_subset_of_le hDN hzD.1, hzD.2⟩
  have hcontact0 : body ∩ sphere 0 = foot 0 := by
    apply Subset.antisymm
    · intro z hz
      rcases hfeet'.symm.subset ⟨hSmark 0 hz.2, hz.1.2⟩ with hf | hf
      · exact hf
      · exact False.elim (disjoint_left.mp hSdisj hz.2 (hfootS 1 hf))
    · exact fun _ hz => ⟨hfootBody 0 hz, hfootS 0 hz⟩
  have hcontact1 : body ∩ sphere 1 = foot 1 := by
    apply Subset.antisymm
    · intro z hz
      rcases hfeet'.symm.subset ⟨hSmark 1 hz.2, hz.1.2⟩ with hf | hf
      · exact False.elim (disjoint_left.mp hSdisj (hfootS 0 hf) hz.2)
      · exact hf
    · exact fun _ hz => ⟨hfootBody 1 hz, hfootS 1 hz⟩
  have houtside (i : Fin 2) : (sphere i \ foot i).Nonempty := by
    obtain ⟨x, hxS, hxW⟩ := hout i
    refine ⟨F x, mem_image_of_mem F hxS, ?_⟩
    intro hxfoot
    have hxR : x ∈ R := ⟨F x, hfootBody i hxfoot, hgF x (hSiC i hxS)⟩
    exact hxW (hRW hxR).2
  have hmodelSphere (i : Fin 2) :
      ∃ b : sphere i ≃ₜ frontier (halfBall 1), b.IsFinitePL := by
    obtain ⟨b, hb, _⟩ := (hsphere i).exists_finitePL_graph_sphere F hFc
      (hFi.mono (hSiC i)) hFPL
    have hboundary : frontier (Metric.closedBall (0 : V3) 1) = Metric.sphere (0 : V3) 1 :=
      frontier_closedBall _ one_ne_zero
    let d := b.symm.trans (Homeomorph.setCongr hboundary.symm)
    have hd : d.IsFinitePL := by
      obtain ⟨f, hf, hfval⟩ := hb.symm
      exact ⟨f, hf, fun x => hfval x⟩
    exact hd.exists_standard_three_sphere_model (isCompact_closedBall _ _)
      (convex_closedBall _ _) ⟨0, Metric.ball_subset_interior_closedBall
        (Metric.mem_ball_self zero_lt_one)⟩ (by simp)
  obtain ⟨b0, hb0⟩ := hmodelSphere 0
  obtain ⟨b1, hb1⟩ := hmodelSphere 1
  let replacement : Set E :=
    ((sphere 0 ∪ sphere 1) ∩ {z | h z ≤ (1 / 2 : ℝ)}) ∪ level
  let Snew : Set X := gx '' replacement
  have hnewSphere : Nonempty (ChartwisePLSphere e Snew) :=
    exists_original_two_foot_height_sphere K hgPL hgi (space_subset_of_le hNK)
      (space_subset_of_le hDN) (hSmark 0) (hSmark 1) b0 hb0 b1 hb1 hball
      (hdisk 0) (hdisk 1) hcontact0 hcontact1 hfeet' (hrim 0) (hrim 1)
      hSdisj (houtside 0) (houtside 1)
  have hBlow (x : X) (hx : x ∈ B) : h (F x) < (1 / 2 : ℝ) := by
    apply lt_of_not_ge
    intro hhigh
    have hxfront := hfront.symm.subset (Or.inl hx)
    have hxD : F x ∈ (A 1).space := hA1.symm.subset (mem_image_of_mem F hxfront)
    have hxR : x ∈ R :=
      ⟨F x, ⟨space_subset_of_le hDN hxD, hhigh⟩, hgF x (hBC hx)⟩
    exact disjoint_left.mp hBW hx (hRW hxR).2
  have hsplit : ((A 1).space ∩ {z | h z ≤ (1 / 2 : ℝ)}) ∪ level =
      (F '' B) ∪ replacement := by
    apply Subset.antisymm
    · rintro z (⟨hzD, hzlow⟩ | hzlevel)
      · obtain ⟨x, hx, rfl⟩ := hA1.subset hzD
        rcases hfront.subset hx with hxB | hxS
        · exact Or.inl (mem_image_of_mem F hxB)
        · apply Or.inr
          apply Or.inl
          refine ⟨?_, hzlow⟩
          rcases hxS with hx0 | hx1
          · exact Or.inl (mem_image_of_mem F hx0)
          · exact Or.inr (mem_image_of_mem F hx1)
      · exact Or.inr (Or.inr hzlevel)
    · rintro z (⟨x, hxB, rfl⟩ | (⟨hzS, hzlow⟩ | hzlevel))
      · exact Or.inl ⟨hA1.symm.subset
          (mem_image_of_mem F (hfront.symm.subset (Or.inl hxB))), (hBlow x hxB).le⟩
      · refine Or.inl ⟨?_, hzlow⟩
        exact hzS.elim (fun hz => hSmark 0 hz) (fun hz => hSmark 1 hz)
      · exact Or.inr hzlevel
  have hgB : gx '' (F '' B) = B := by
    apply Subset.antisymm
    · rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hgF x (hBC hx)]
    · intro x hx
      exact ⟨F x, mem_image_of_mem F hx, hgF x (hBC hx)⟩
  have hfullFront : frontier (L ∪ R) = B ∪ Snew := by
    change frontier (L ∪ R) = B ∪ (gx '' replacement)
    rw [hfrontUnion, hsplit, image_union, hgB]
  have hBnew : Disjoint B Snew := by
    apply disjoint_left.mpr
    rintro x hxB ⟨z, hz, hgz⟩
    rcases hz with ⟨hzS, _⟩ | hzlevel
    · rcases hzS with hz0 | hz1
      · obtain ⟨y, hy, rfl⟩ := hz0
        have hyx : y = x := (hgF y (hSiC 0 hy)).symm.trans hgz
        exact disjoint_left.mp (hBS 0) hxB (hyx ▸ hy)
      · obtain ⟨y, hy, rfl⟩ := hz1
        have hyx : y = x := (hgF y (hSiC 1 hy)).symm.trans hgz
        exact disjoint_left.mp (hBS 1) hxB (hyx ▸ hy)
    · have hxR : x ∈ R := ⟨z, ⟨hzlevel.1, hzlevel.2.ge⟩, hgz⟩
      exact disjoint_left.mp hBW hxB (hRW hxR).2
  have hbodyK : body ⊆ K.space := fun _ hz => space_subset_of_le hNK hz.1
  have hRconn : IsConnected R := hball.isConnected.image gx
    ((continuous_subtype_val.comp_continuousOn hgc).mono hbodyK)
  have hattach : (L ∩ R).Nonempty := by
    refine ⟨q 0, he.closed.frontier_subset (hSL 0 hzero), ?_⟩
    have hpheight : h (p 0) = 1 := (hvalues _ ((hA 2).1 (hpA 0))).1 (hpA 0)
    refine ⟨p 0, ⟨N.vertices_subset_space (hAN (hpA 0)), ?_⟩, ?_⟩
    · change (1 / 2 : ℝ) ≤ h (p 0)
      rw [hpheight]
      norm_num
    · rw [hp0]
      exact hgF (q 0) (hSiC 0 hzero)
  exact ⟨R, Snew, hRc, hRconn, fun x hx => (hRW hx).2,
    hRPL, hUnionPL, hnewSphere, hfullFront, hBnew, hattach⟩

end PoincareConjecture.M76
