#![cfg(all(feature = "std", feature = "rocksdb"))]
use bitvec::{order::Msb0, vec::BitVec, view::BitView};
use pathfinder_common::{felt, hash::PedersenHash, trie::TrieNode};
use pathfinder_crypto::Felt as PathfinderFelt;
use pathfinder_merkle_tree::tree::{MerkleTree, TestStorage};
use pathfinder_storage::{Node, StoredNode};
use rand::Rng;
use starknet_types_core::{felt::Felt, hash::Pedersen};
use std::collections::HashMap;
use pathfinder_common::hash::FeltHash;

use crate::{
    databases::{create_rocks_db, RocksDB, RocksDBConfig},
    id::{BasicId, BasicIdBuilder},
    trie::merkle_tree::{Membership, ProofNode},
    BonsaiStorage, BonsaiStorageConfig,
};

/// Commits the tree changes and persists them to storage.
fn commit_and_persist(
    tree: MerkleTree<PedersenHash, 251>,
    storage: &mut TestStorage,
) -> (PathfinderFelt, u64) {
    use pathfinder_storage::Child;

    for (key, value) in &tree.leaves {
        let key = PathfinderFelt::from_bits(key).unwrap();
        storage.leaves.insert(key, *value);
    }

    let update = tree.commit(storage).unwrap();

    let mut indices = HashMap::new();
    let mut idx = storage.nodes.len();
    for hash in update.nodes.keys() {
        indices.insert(*hash, idx as u64);
        idx += 1;
    }

    for (hash, node) in update.nodes {
        let node = match node {
            Node::Binary { left, right } => {
                let left = match left {
                    Child::Id(idx) => idx,
                    Child::Hash(hash) => {
                        *indices.get(&hash).expect("Left child should have an index")
                    }
                };

                let right = match right {
                    Child::Id(idx) => idx,
                    Child::Hash(hash) => *indices
                        .get(&hash)
                        .expect("Right child should have an index"),
                };

                StoredNode::Binary { left, right }
            }
            Node::Edge { child, path } => {
                let child = match child {
                    Child::Id(idx) => idx,
                    Child::Hash(hash) => *indices.get(&hash).expect("Child should have an index"),
                };

                StoredNode::Edge { child, path }
            }
            Node::LeafBinary => StoredNode::LeafBinary,
            Node::LeafEdge { path } => StoredNode::LeafEdge { path },
        };

        storage
            .nodes
            .insert(*indices.get(&hash).unwrap(), (hash, node));
    }

    let index = *indices.get(&update.root).unwrap();

    (update.root, index)
}

fn assert_eq_proof(bonsai_proof: &[ProofNode], pathfinder_proof: &[TrieNode]) {
    for (bonsai_node, pathfinder_node) in bonsai_proof.iter().zip(pathfinder_proof.iter()) {
        match (bonsai_node, pathfinder_node) {
            (
                ProofNode::Binary { left, right },
                pathfinder_common::trie::TrieNode::Binary {
                    left: pathfinder_left,
                    right: pathfinder_right,
                },
            ) => {
                let pathfinder_left_bits = pathfinder_left.to_hex_str();
                let pathfinder_felt = Felt::from_hex(&pathfinder_left_bits).unwrap();
                assert_eq!(left, &pathfinder_felt);
                let pathfinder_right_bits = pathfinder_right.to_hex_str();
                let pathfinder_felt = Felt::from_hex(&pathfinder_right_bits).unwrap();
                assert_eq!(right, &pathfinder_felt);
            }
            (
                ProofNode::Edge { child, path },
                pathfinder_common::trie::TrieNode::Edge {
                    child: pathfinder_child,
                    path: pathfinder_path,
                },
            ) => {
                let pathfinder_child_bits = pathfinder_child.to_hex_str();
                let pathfinder_felt = Felt::from_hex(&pathfinder_child_bits).unwrap();
                assert_eq!(child, &pathfinder_felt);
                assert_eq!(&path.0, pathfinder_path);
            }
            _ => panic!("Proofs are not the same"),
        }
    }
}

#[test]
fn debug_deoxys() {
    // Load storage_data.json file
    let storage_data = include_str!("storage_data.json");
    let storage_data: Vec<Vec<(String, String)>> = serde_json::from_str(storage_data).unwrap();
    let tempdir = tempfile::tempdir().unwrap();
    let db = create_rocks_db(tempdir.path()).unwrap();
    let config = BonsaiStorageConfig::default();
    let mut storage = pathfinder_merkle_tree::tree::TestStorage::default();
    let mut id_builder = BasicIdBuilder::new();
    let mut bonsai_storage =
        BonsaiStorage::<_, _, Pedersen>::new(RocksDB::new(&db, RocksDBConfig::default()), config)
            .unwrap();
    let mut pathfinder_merkle_tree: MerkleTree<PedersenHash, 251> =
        pathfinder_merkle_tree::tree::MerkleTree::empty();
    let identifier =
        Felt::from_hex("0x04acd4b2a59eae7196f6a5c26ead8cb5f9d7ad3d911096418a23357bb2eac075")
            .unwrap()
            .to_bytes_be()
            .to_vec();
    for block_changes in storage_data.iter() {
        for pair in block_changes.iter() {
            let key = keyer(Felt::from_hex(&pair.0).unwrap());
            let value = Felt::from_hex(&pair.1).unwrap();
            bonsai_storage.insert(&identifier, &key, &value).unwrap();
            pathfinder_merkle_tree
                .set(
                    &storage,
                    key,
                    PathfinderFelt::from_hex_str(&pair.1).unwrap(),
                )
                .unwrap();
        }
        bonsai_storage.commit(id_builder.new_id()).unwrap();
        let (_, root_id) = commit_and_persist(pathfinder_merkle_tree.clone(), &mut storage);
        let pathfinder_root = storage.nodes.get(&root_id).unwrap().0;
        let bonsai_root = bonsai_storage.root_hash(&identifier).unwrap();
        println!("{:#02x}", bonsai_root);
        println!("{:#02x}", pathfinder_root);
        assert_eq!(pathfinder_root.to_be_bytes(), bonsai_root.to_bytes_be());
    }
}

fn keyer(felt: Felt) -> BitVec<u8, Msb0> {
    felt.to_bytes_be().view_bits()[5..].to_bitvec()
}

#[test]
fn basic_proof() {
    let identifier = vec![];
    let tempdir = tempfile::tempdir().unwrap();
    let db = create_rocks_db(tempdir.path()).unwrap();
    let config = BonsaiStorageConfig::default();
    let mut storage = pathfinder_merkle_tree::tree::TestStorage::default();
    let mut bonsai_storage =
        BonsaiStorage::<_, _, Pedersen>::new(RocksDB::new(&db, RocksDBConfig::default()), config)
            .unwrap();
    let mut pathfinder_merkle_tree: MerkleTree<PedersenHash, 251> =
        pathfinder_merkle_tree::tree::MerkleTree::empty();
    let mut id_builder = BasicIdBuilder::new();
    let pair1 = (
        vec![1, 2, 1],
        Felt::from_hex("0x66342762FDD54D033c195fec3ce2568b62052e").unwrap(),
    );
    let bitvec = BitVec::from_vec(pair1.0.clone());
    bonsai_storage
        .insert(&identifier, &bitvec, &pair1.1)
        .unwrap();
    pathfinder_merkle_tree
        .set(
            &storage,
            bitvec,
            PathfinderFelt::from_hex_str("0x66342762FDD54D033c195fec3ce2568b62052e").unwrap(),
        )
        .unwrap();
    let pair2 = (
        vec![1, 2, 2],
        Felt::from_hex("0x66342762FD54D033c195fec3ce2568b62052e").unwrap(),
    );
    let bitvec = BitVec::from_vec(pair2.0.clone());
    bonsai_storage
        .insert(&identifier, &bitvec, &pair2.1)
        .unwrap();
    pathfinder_merkle_tree
        .set(
            &storage,
            bitvec,
            PathfinderFelt::from_hex_str("0x66342762FD54D033c195fec3ce2568b62052e").unwrap(),
        )
        .unwrap();
    let pair3 = (
        vec![1, 2, 3],
        Felt::from_hex("0x66342762FD54D033c195fec3ce2568b62052e").unwrap(),
    );
    let bitvec = BitVec::from_vec(pair3.0.clone());
    bonsai_storage
        .insert(&identifier, &bitvec, &pair3.1)
        .unwrap();
    pathfinder_merkle_tree
        .set(
            &storage,
            bitvec,
            PathfinderFelt::from_hex_str("0x66342762FD54D033c195fec3ce2568b62052e").unwrap(),
        )
        .unwrap();
    bonsai_storage.commit(id_builder.new_id()).unwrap();
    let (_, root_id) = commit_and_persist(pathfinder_merkle_tree.clone(), &mut storage);
    let bonsai_proof = bonsai_storage
        .get_proof(&identifier, &BitVec::from_vec(vec![1, 2, 1]))
        .unwrap();
    let pathfinder_proof =
        pathfinder_merkle_tree::tree::MerkleTree::<PedersenHash, 251>::get_proof(
            root_id,
            &storage,
            &BitVec::from_vec(vec![1, 2, 1]),
        )
        .unwrap();
    assert_eq_proof(&bonsai_proof, &pathfinder_proof);
    assert_eq!(
        BonsaiStorage::<BasicId, RocksDB<BasicId>, Pedersen>::verify_proof(
            bonsai_storage.root_hash(&identifier).unwrap(),
            &BitVec::from_vec(vec![1, 2, 1]),
            pair1.1,
            &bonsai_proof
        ),
        Some(Membership::Member)
    );
}

#[test]
fn multiple_proofs() {
    let identifier = vec![];
    let tempdir = tempfile::tempdir().unwrap();
    let db = create_rocks_db(tempdir.path()).unwrap();
    let config = BonsaiStorageConfig::default();
    let mut storage = pathfinder_merkle_tree::tree::TestStorage::default();
    let mut bonsai_storage =
        BonsaiStorage::<_, _, Pedersen>::new(RocksDB::new(&db, RocksDBConfig::default()), config)
            .unwrap();
    let mut pathfinder_merkle_tree: MerkleTree<PedersenHash, 251> =
        pathfinder_merkle_tree::tree::MerkleTree::empty();
    let mut id_builder = BasicIdBuilder::new();
    let mut rng = rand::thread_rng();
    let tree_size = rng.gen_range(10..1000);
    let mut elements = vec![];
    for _ in 0..tree_size {
        let mut element = String::from("0x");
        let element_size = rng.gen_range(10..32);
        for _ in 0..element_size {
            let random_byte: u8 = rng.gen();
            element.push_str(&format!("{:02x}", random_byte));
        }
        let value = Felt::from_hex(&element).unwrap();
        let key = &value.to_bytes_be()[..31];
        bonsai_storage
            .insert(&identifier, &BitVec::from_vec(key.to_vec()), &value)
            .unwrap();
        pathfinder_merkle_tree
            .set(
                &storage,
                BitVec::from_vec(key.to_vec()),
                PathfinderFelt::from_hex_str(&element).unwrap(),
            )
            .unwrap();
        elements.push((key.to_vec(), value));
    }
    bonsai_storage.commit(id_builder.new_id()).unwrap();
    let (_, root_id) = commit_and_persist(pathfinder_merkle_tree.clone(), &mut storage);
    for element in elements.iter() {
        let proof = bonsai_storage
            .get_proof(&identifier, &BitVec::from_vec(element.0.clone()))
            .unwrap();
        let pathfinder_proof =
            pathfinder_merkle_tree::tree::MerkleTree::<PedersenHash, 251>::get_proof(
                root_id,
                &storage,
                &BitVec::from_vec(element.0.clone()),
            )
            .unwrap();
        assert_eq_proof(&proof, &pathfinder_proof);
        assert_eq!(
            BonsaiStorage::<BasicId, RocksDB<BasicId>, Pedersen>::verify_proof(
                bonsai_storage.root_hash(&identifier).unwrap(),
                &BitVec::from_vec(element.0.clone()),
                element.1,
                &proof
            ),
            Some(Membership::Member)
        );
    }
}

#[test]
fn one_element_proof() {
    let identifier = vec![];
    let tempdir = tempfile::tempdir().unwrap();
    let db = create_rocks_db(tempdir.path()).unwrap();
    let config = BonsaiStorageConfig::default();
    let mut storage = pathfinder_merkle_tree::tree::TestStorage::default();
    let mut bonsai_storage =
        BonsaiStorage::<_, _, Pedersen>::new(RocksDB::new(&db, RocksDBConfig::default()), config)
            .unwrap();
    let mut pathfinder_merkle_tree: MerkleTree<PedersenHash, 251> =
        pathfinder_merkle_tree::tree::MerkleTree::empty();
    let mut id_builder = BasicIdBuilder::new();
    let pair1 = (
        vec![1, 2, 1],
        Felt::from_hex("0x66342762FDD54D033c195fec3ce2568b62052e").unwrap(),
    );
    let bitvec = BitVec::from_vec(pair1.0.clone());
    bonsai_storage
        .insert(&identifier, &bitvec, &pair1.1)
        .unwrap();
    pathfinder_merkle_tree
        .set(
            &storage,
            bitvec,
            PathfinderFelt::from_hex_str("0x66342762FDD54D033c195fec3ce2568b62052e").unwrap(),
        )
        .unwrap();
    bonsai_storage.commit(id_builder.new_id()).unwrap();
    let (_, root_id) = commit_and_persist(pathfinder_merkle_tree.clone(), &mut storage);
    let bonsai_proof = bonsai_storage
        .get_proof(&identifier, &BitVec::from_vec(vec![1, 2, 1]))
        .unwrap();
    let pathfinder_proof =
        pathfinder_merkle_tree::tree::MerkleTree::<PedersenHash, 251>::get_proof(
            root_id,
            &storage,
            &BitVec::from_vec(vec![1, 2, 1]),
        )
        .unwrap();
    assert_eq_proof(&bonsai_proof, &pathfinder_proof);
    assert_eq!(
        BonsaiStorage::<BasicId, RocksDB<BasicId>, Pedersen>::verify_proof(
            bonsai_storage.root_hash(&identifier).unwrap(),
            &BitVec::from_vec(vec![1, 2, 1]),
            pair1.1,
            &bonsai_proof
        ),
        Some(Membership::Member)
    );
}

#[test]
fn successfully_forge_proof() {
    let mut storage = TestStorage::default();

    let mut pathfinder_merkle_tree: MerkleTree<PedersenHash, 251> = MerkleTree::empty();
    let mut i: u64 = 0;
    while i < 2000 {
        let key = PedersenHash::hash(felt!("0x0"), PathfinderFelt::from_u64(i));
        let value = PedersenHash::hash(key.clone(), key.clone());
        pathfinder_merkle_tree
            .set(
                &storage,
                key.clone().view_bits().to_bitvec(),
                value.into(),
            )
            .unwrap();

       pathfinder_merkle_tree.set(&storage, key.view_bits().to_bitvec(), value).unwrap();
        i += 1;
    }

    let (commitment, index) = commit_and_persist(pathfinder_merkle_tree.clone(), &mut storage);
    let key = PedersenHash::hash(felt!("0x0"), PathfinderFelt::from_u64(33));
    let valid_value = PedersenHash::hash(key.clone(), key.clone());

    let mut pathfinder_proof = MerkleTree::<PedersenHash, 251>::get_proof(index, &storage, &*key.view_bits().to_bitvec()).unwrap();
    let mut bonsai_proof: Vec<ProofNode> = pathfinder_proof.into_iter().map(ProofNode::from).collect();

    // This is what the valid proof looks like:
    // let root = 0x04946c7636b878064ddaab68a34c440f7961b854934e9b7347d981f9f5f768f2;
    // let key = 0x066488017aeba3e8d5a2074c8113b076f7e624fa97a1933623e5ba034d22e555;
    // let proof = array![
    //     TrieNode::Binary(BinaryNodeImpl::new(0x01f387675be9603ca64faee950fc41c70c4e8c534fb9ac6d235bf7ef732fdbb6,0x01bdac12073dd4161c28740f654bdd4162aad1e8c0588989f7d05977fc5ef41e)),
    //     TrieNode::Binary(BinaryNodeImpl::new(0x00f618893b917332d0f527205f94ab7bd8ab20da5b60be66f22b90d08100aba4,0x0001e996b4969876b0d24e9c9446f9aa9efef959462e2a9e800945942d4d0b63)),
    //     TrieNode::Binary(BinaryNodeImpl::new(0x07cf400d095212c51ce3320971de539643d8eabaffb4c2a4369e222f3606f03a,0x0321dba462885b2a1969701b2c9efebb1407a0c1108fe27da6f54db7808721d2)),
    //     TrieNode::Binary(BinaryNodeImpl::new(0x02051cd969f864999bb8849bc81b7f9269da475cfe3917572ee45019c1848bbf,0x06a08b555530572d8ef951bcc258775dd8f9a16491b5ef9ce1d6487469b09cd3)),
    //     TrieNode::Binary(BinaryNodeImpl::new(0x02827a2dd7fed7114104184561c21b38d79ec0b1702adb234392b8d9905818b4,0x051e8aeb18901009d0d3df64f3642ce60b139c46a2f8ca618bbf6dcf3b27679b)),
    //     TrieNode::Binary(BinaryNodeImpl::new(0x01e526c4030bf33ce4be9b7029652b3c57a63623817d5f72edda770441755b48,0x02e5b904361ae2272b75fc7e9bdfc271547f0ec4baea5830431ef0600f91622b)),
    //     TrieNode::Binary(BinaryNodeImpl::new(0x04d3adf75cac7938edf92e395c8ab056f87f4c97b594f834a7b7b8086651e615,0x07bf353cef62649614805b0afb71a68bea111943398ccf6708b018299eceef08)),
    //     TrieNode::Binary(BinaryNodeImpl::new(0x02a4a2338d90a7d7ce22adc430c5600761151e5f2c1ac9b4d9804ddbabaf4989,0x02ee6c70d6f243e1255be910c52bb5416962bd0dee3ef3cde567ffa311e73f37)),
    //     TrieNode::Binary(BinaryNodeImpl::new(0x030a9e7caa6a8429fbd73f5e1ea5061e586b044b631368b27401071c8bc6985a,0x013689ea58dffd14f77c212d485ac79c1f1770d4ab5de94f745b41eb1ca6a750)),
    //     TrieNode::Binary(BinaryNodeImpl::new(0x040edfc2b946ee3af0c01e29b8730acc152a4c371ff9a89d8e4898d6cd57505f,0x042ab88780b5891adb125bcfcaf3f6cf9adeb1639609156668faf9c2d8fd5bc7)),
    //     TrieNode::Binary(BinaryNodeImpl::new(0x06e5ffbc0b2dc82ea66cb5ff715ef6fc5b3f37d85c1c4114b39731bdc14fad61,0x0715e3724d0fc71047a1e432d5967f4c9b22eccc809ac53bcd002e70caf02930)),
    //     TrieNode::Edge(EdgeNodeImpl::new(0x80, 0x06c45f152061e861397038a59dacc35e75a908bdd2f0424332c759904bc5e3b2, 1)),
    //     TrieNode::Binary(BinaryNodeImpl::new(0x02be2c76a8d7e1169bd74d024e32ac4164d887ebde370a0721d7a18136e434ba,0x01e61e1f576c6d6bfae08d5a5b99ea2f918c5dea81191ef31f683d0a71c02c49)),
    //     TrieNode::Edge(EdgeNodeImpl::new(0x08017aeba3e8d5a2074c8113b076f7e624fa97a1933623e5ba034d22e555, 0x02ca0f0f20113199ab071dcd6b0a8264410b1680b1e08e4653e80850ccdb3640, 238))
    // ];

    // this proof should pass
    assert_eq!(
        BonsaiStorage::<BasicId, RocksDB<BasicId>, Pedersen>::verify_proof(Felt::from_bytes_be(commitment.as_be_bytes()), &*key.view_bits().to_bitvec(), Felt::from_bytes_be(valid_value.as_be_bytes()), bonsai_proof.as_slice()),
        Some(Membership::Member)
    );

    // we can now forge the proof, by setting the value to the value of a preceding edge node
    let invalid_value = Felt::from_hex("0x06c45f152061e861397038a59dacc35e75a908bdd2f0424332c759904bc5e3b2").unwrap(); // this is a node binary_node hash
    // and removing the final two proof nodes. This is possible as we do not ensure the key was evaluated all the way.
    let forged_proof = &bonsai_proof[..12];

    // this should def not pass
    assert_eq!(
        BonsaiStorage::<BasicId, RocksDB<BasicId>, Pedersen>::verify_proof(Felt::from_bytes_be(commitment.as_be_bytes()), &*key.view_bits().to_bitvec(), invalid_value, forged_proof),
        Some(Membership::Member)
    );
}

#[test]
fn zero_not_crashing() {
    let identifier = vec![];
    let tempdir = tempfile::tempdir().unwrap();
    let db = create_rocks_db(tempdir.path()).unwrap();
    let config = BonsaiStorageConfig::default();
    let mut bonsai_storage =
        BonsaiStorage::<_, _, Pedersen>::new(RocksDB::new(&db, RocksDBConfig::default()), config)
            .unwrap();
    let mut id_builder = BasicIdBuilder::new();
    bonsai_storage.commit(id_builder.new_id()).unwrap();
    bonsai_storage
        .get_proof(&identifier, &BitVec::from_vec(vec![1, 2, 1]))
        .expect_err("Should error");
}
