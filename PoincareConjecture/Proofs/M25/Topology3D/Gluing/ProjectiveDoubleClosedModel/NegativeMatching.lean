import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveDoubleClosedModel.NegativeBallChart
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveCapBallChart
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.SchoenfliesBallMatching










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M} {C1 C2 : ClosedModelCapData g}
  {P2 : PoincareConjecture.StandardPuncturedProjectiveCover M C2.puncture C2.carrier}




theorem NegativeProjectiveSideData.exists_matched_ball
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    (P1 : PoincareConjecture.StandardPuncturedProjectiveCover
      M C1.puncture C1.carrier)
    (d : NegativeProjectiveSideData C1 C2 P2) :
    let ell := C1.epsilon⁻¹
    let c := (d.v + ell) / 2
    let h := (ell - d.v) / 4
    let a := c - h * (3 / 4)
    let b := c - h * (1 / 2)
    let V := interior (C1.carrier \ C1.region b ell)
    ∃ (F : RoundCylinderSpace → UnitThreeSphere)
      (G : OpenPartialHomeomorph UnitThreeSphere M),
      let L := F '' (univ ×ˢ Ioo a b)
      let U0 := projectiveCoverDomain C1.puncture ∩ P1.cover ⁻¹' V
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ G G.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ G.symm G.target ∧
      V ∪ G.target = C1.carrier ∪ C2.carrier ∧
      V ∩ G.target = C1.region a b ∧
      EqOn G P1.cover L ∧
      G.source ∩ G ⁻¹' C1.region a b = L ∧
      IsOpen U0 ∧
      (∀ x : UnitThreeSphere, -x ∈ U0 ↔ x ∈ U0) ∧
      Disjoint G.source ((fun x : UnitThreeSphere => -x) '' G.source) ∧
      U0 ∪ G.source ∪ (fun x : UnitThreeSphere => -x) '' G.source = univ ∧
      U0 ∩ G.source = L := by
  classical
  let H := C1.epsilon⁻¹
  let Omega : Set RoundCylinderSpace := univ ×ˢ Ioo (-H) H
  let Y := C1.carrier ∪ C2.carrier
  let N := C1
  let K : ℝ → Set M := fun s => C1.carrier \ N.region s H
  let V : ℝ → Set M := fun s => interior (K s)
  let W : ℝ → Set M := fun s => Y \ K s
  let c := (d.v + H) / 2
  let h := (H - d.v) / 4
  let a := c - h * (3 / 4)
  let b := c - h * (1 / 2)
  have hv : d.v ∈ Ioo (-H) H := d.v_mem
  have hh : 0 < h := by dsimp [h]; linarith [hv.2]
  have hleft : d.v < c - h := by dsimp [c, h]; linarith [hv.2]
  have hright : c + h < H := by dsimp [c, h]; linarith [hv.2]
  have hva : d.v < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hbH : b < H := by dsimp [b]; linarith
  obtain ⟨J2, hJ2s, hJ2t, hJ2, hJ2i, _, hJ2ray, hJ2annulus⟩ := d.exists_ball_chart
  obtain ⟨_, _, hcover, hinter, _⟩ := d.cuts a b hva hab hbH
  change V b ∪ W a = Y at hcover
  change V b ∩ W a = N.region a b at hinter
  change J2.source = W a at hJ2s
  obtain ⟨p0, F, hp0, hFD, hFc, _, hFinj, _, hends,
    hpsi1, S1, J1, _, _, _, hJ1s, hJ1t, hJ1, hJ1i, _, _, _,
    hJ1annulus, _, hJ1collar, _⟩ :=
    capCertificate_exists_projective_buffered_ball_chart hS C1 P1 c h hh
      (hv.1.trans hleft) hright
  let B : ℝ → Set UnitThreeSphere := fun s => F '' (univ ×ˢ Ioo s H) ∪ {p0}
  let L : Set UnitThreeSphere := F '' (univ ×ˢ Ioo a b)
  let U0 : Set UnitThreeSphere := projectiveCoverDomain C1.puncture ∩ P1.cover ⁻¹' V b
  obtain ⟨Z, hZs, hZt, hZ, hZi, _, _, hZcollar, _, hZannulus, _⟩ :=
    SchoenfliesData.exists_sameHeight_ball_chart hD S1 d.S hpsi1 d.collar
  let J := J1.trans' Z (hJ1t.trans hZs.symm)
  let G := J.trans' J2.symm (hZt.trans hJ2t.symm)
  have hGs : G.source = B a := hJ1s
  have hGt : G.target = W a := hJ2s
  have hJ1Z {x : UnitThreeSphere} (hx : x ∈ J1.source) : J1 x ∈ Z.source :=
    hZs.symm ▸ hJ1t ▸ J1.map_source hx
  have hZJ2 {x : UnitThreeSphere} (hx : x ∈ J1.source) : Z (J1 x) ∈ J2.target :=
    hJ2t.symm ▸ hZt ▸ Z.map_source (hJ1Z hx)
  have hJ2Z {x : M} (hx : x ∈ J2.source) : J2 x ∈ Z.target :=
    hZt.symm ▸ hJ2t ▸ J2.map_source hx
  have hZJ1 {x : M} (hx : x ∈ J2.source) : Z.symm (J2 x) ∈ J1.target :=
    hJ1t.symm ▸ hZs ▸ Z.map_target (hJ2Z hx)
  have hG : ContMDiffOn (𝓡 3) (𝓡 3) ∞ G G.source := by
    change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => J2.symm (Z (J1 x))) J1.source
    exact hJ2i.comp (hZ.comp hJ1 (fun _ hx => hJ1Z hx)) (fun _ hx => hZJ2 hx)
  have hGi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ G.symm G.target := by
    change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => J1.symm (Z.symm (J2 x))) J2.source
    exact hJ1i.comp (hZi.comp hJ2 (fun _ hx => hJ2Z hx)) (fun _ hx => hZJ1 hx)
  have hGray (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Ico (1 / 2 : ℝ) (3 / 4)) :
      F (q, c - h * t) ∈ G.source ∧
      G (F (q, c - h * t)) = N.coordinate_map (q, c - h * t) := by
    have ht' : t ∈ Ico (1 / 4 : ℝ) (3 / 4) := ⟨by linarith [ht.1], ht.2⟩
    refine ⟨(hJ1collar q t ht').1, ?_⟩
    change J2.symm (Z (J1 (F (q, c - h * t)))) = _
    rw [(hJ1collar q t ht').2, hZcollar q t ⟨ht.1, ht.2.le⟩]
    exact (hJ2ray q t ⟨ht.1, ht.2.le⟩).1
  have haH : a ∈ Ioo (-H) H := ⟨hv.1.trans hva, hab.trans hbH⟩
  have hbstrip : b ∈ Ioo (-H) H := ⟨haH.1.trans hab, hbH⟩
  have hLOmega : univ ×ˢ Ioo a b ⊆ Omega := fun _ hz =>
    ⟨mem_univ _, haH.1.trans hz.2.1, hz.2.2.trans hbH⟩
  have hLs : L ⊆ G.source := by
    rintro x ⟨z, hz, rfl⟩
    rw [hGs]
    exact Or.inl ⟨z, ⟨mem_univ _, hz.2.1, hz.2.2.trans hbH⟩, rfl⟩
  have hEqOn : EqOn G P1.cover L := by
    rintro x ⟨⟨q, s⟩, hz, rfl⟩
    have ht : (c - s) / h ∈ Ico (1 / 2 : ℝ) (3 / 4) := by
      constructor
      · apply le_of_lt
        apply (lt_div_iff₀ hh).mpr
        dsimp only [b] at hz
        linarith [hz.2.2]
      · apply (div_lt_iff₀ hh).mpr
        dsimp only [a] at hz
        linarith [hz.2.1]
    have hcs : c - h * ((c - s) / h) = s := by field_simp; ring
    have heq := (hGray q ((c - s) / h) ht).2
    rw [hcs] at heq
    exact heq.trans (hFc (hLOmega hz)).symm
  have hregionJ2 : N.region a b ⊆ J2.source := by
    intro x hx
    have hmem : x ∈ V b ∩ W a := hinter.symm ▸ hx
    exact hJ2s.symm ▸ hmem.2
  have hJ2inverseAnnulus : J2.symm ''
      {z : E3 | d.S.radial (1 / 2) < ‖z‖ ∧ ‖z‖ < d.S.radial (3 / 4)} =
        N.region a b := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hJ2annulus.symm ▸ hz
      rw [J2.left_inv (hregionJ2 hx)]
      exact hx
    · intro x hx
      exact ⟨J2 x, hJ2annulus ▸ mem_image_of_mem J2 hx, J2.left_inv (hregionJ2 hx)⟩
  have hGimage : G '' L = N.region a b := by
    calc
      G '' L = J2.symm '' (Z '' (J1 '' L)) := by
        symm
        calc
          J2.symm '' (Z '' (J1 '' L)) = (J2.symm ∘ Z) '' (J1 '' L) :=
            image_image _ _ _
          _ = ((J2.symm ∘ Z) ∘ J1) '' L := image_image _ _ _
          _ = G '' L := rfl
      _ = N.region a b := by rw [hJ1annulus, hZannulus, hJ2inverseAnnulus]
  have hGpreimage : G.source ∩ G ⁻¹' N.region a b = L := by
    apply Subset.antisymm
    · rintro x ⟨hxs, hx⟩
      obtain ⟨y, hy, heq⟩ := hGimage.symm ▸ hx
      exact (G.injOn (hLs hy) hxs heq) ▸ hy
    · intro x hx
      exact ⟨hLs hx, hGimage ▸ mem_image_of_mem G hx⟩
  obtain ⟨_, _, _, hVb, _, _, _⟩ := C1.end_neck_lower_cut_topology hbstrip
  change V b = C1.closed_core ∪ N.region (-H) b at hVb
  have hKsub : K a ⊆ V b := by
    intro x hx
    rw [hVb]
    by_cases hxN : x ∈ N.end_chart.target
    · have hxI : (N.coordinate_inverse x).2 ∈ Ioo (-H) H :=
        (N.coordinate_inverse_mem x hxN).2
      have hxa : (N.coordinate_inverse x).2 ≤ a := by
        by_contra hlt
        exact hx.2 ⟨hxN, lt_of_not_ge hlt, hxI.2⟩
      exact Or.inr ⟨hxN, hxI.1, hxa.trans_lt hab⟩
    · apply Or.inl
      rw [C1.closed_core_eq_complement_end]
      exact ⟨hx.1, hxN⟩
  have hU0open : IsOpen U0 :=
    P1.local_diffeomorph.contMDiffOn.continuousOn.isOpen_inter_preimage
      (isOpen_projectiveCoverDomain C1.puncture) isOpen_interior
  have hUneg (x : UnitThreeSphere) (hx : x ∈ U0) : -x ∈ U0 := by
    refine ⟨(neg_mem_projectiveCoverDomain_iff C1.puncture x).mpr hx.1, ?_⟩
    change P1.cover (-x) ∈ V b
    rw [StandardPuncturedProjectiveCover.cover_neg P1 hx.1]
    exact hx.2
  have hUnegIff (x : UnitThreeSphere) : -x ∈ U0 ↔ x ∈ U0 := by
    constructor
    · intro hx
      simpa only [neg_neg] using hUneg (-x) hx
    · exact hUneg x
  obtain ⟨_, _, _, _, _, _, hBdis, hBcomp⟩ := hends a haH
  have hGdis : Disjoint G.source ((fun x : UnitThreeSphere => -x) '' G.source) := by
    rw [hGs]
    exact hBdis.mono subset_closure (image_mono subset_closure)
  have hwhole : U0 ∪ G.source ∪ (fun x : UnitThreeSphere => -x) '' G.source = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ G.source
    · exact Or.inl (Or.inr hx)
    by_cases hxn : x ∈ (fun y : UnitThreeSphere => -y) '' G.source
    · exact Or.inr hxn
    have hout : x ∈ (B a ∪ (fun y : UnitThreeSphere => -y) '' B a)ᶜ := by
      rw [← hGs]
      exact fun hmem => hmem.elim hx hxn
    have hpre : x ∈ projectiveCoverDomain C1.puncture ∩ P1.cover ⁻¹' K a :=
      hBcomp.symm ▸ hout
    exact Or.inl (Or.inl ⟨hpre.1, hKsub hpre.2⟩)
  have hNdomain {z : RoundCylinderSpace} (hz : z ∈ Omega) :
      z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := hz.2
  have hUinter : U0 ∩ G.source = L := by
    apply Subset.antisymm
    · rintro x ⟨hxU, hxG⟩
      have hxB : x ∈ B a := hGs ▸ hxG
      rcases hxB with hxB | hxB
      · obtain ⟨⟨q, s⟩, hz, rfl⟩ := hxB
        have hzO : (q, s) ∈ Omega := ⟨mem_univ _, haH.1.trans hz.2.1, hz.2.2⟩
        have hxN : N.coordinate_map (q, s) ∈ N.end_chart.target :=
          N.coordinate_map_mem ⟨mem_univ _, hNdomain hzO⟩
        have hxV : P1.cover (F (q, s)) ∈ V b := hxU.2
        have hcoverEq : P1.cover (F (q, s)) = N.coordinate_map (q, s) := hFc hzO
        rw [hcoverEq, hVb] at hxV
        have hsb : s < b := by
          rcases hxV with hxcore | hxlow
          · rw [C1.closed_core_eq_complement_end] at hxcore
            exact (hxcore.2 hxN).elim
          · have hlt := hxlow.2.2
            rwa [N.coordinate_inverse_map (q, s) (hNdomain hzO)] at hlt
        exact ⟨(q, s), ⟨mem_univ _, hz.2.1, hsb⟩, rfl⟩
      · have hx0 : x = p0 := mem_singleton_iff.mp hxB
        subst x
        exact (hxU.1 hp0).elim
    · rintro x ⟨z, hz, rfl⟩
      have hzO := hLOmega hz
      refine ⟨⟨hFD hzO, ?_⟩, hLs ⟨z, hz, rfl⟩⟩
      change P1.cover (F z) ∈ V b
      have hcoverEq : P1.cover (F z) = N.coordinate_map z := hFc hzO
      rw [hcoverEq, hVb]
      refine Or.inr ⟨N.coordinate_map_mem ⟨mem_univ _, hNdomain hzO⟩, ?_⟩
      rw [N.coordinate_inverse_map z (hNdomain hzO)]
      exact ⟨hzO.2.1, hz.2.2⟩
  refine ⟨F, G, hG, hGi, ?_, ?_, hEqOn, hGpreimage, hU0open,
    hUnegIff, hGdis, hwhole, hUinter⟩
  · rw [hGt]
    exact hcover
  · rw [hGt]
    exact hinter

end PoincareConjecture.M25.Topology3D
