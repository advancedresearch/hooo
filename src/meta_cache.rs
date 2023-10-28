use crate::*;

use piston_meta::{Range, MetaData};
use std::sync::{Arc, Mutex};
use serde::{Serialize, Deserialize};

#[derive(Hash, PartialEq, Eq)]
pub struct Key {
    pub source: Arc<String>,
    pub syntax: Arc<String>,
}

pub struct MetaCache {
    pub cache: Arc<Mutex<HashMap<Key, Result<Vec<Range<MetaData>>, String>>>>,
}

impl MetaCache {
    pub fn new() -> MetaCache {
        MetaCache {
            cache: Arc::new(HashMap::new().into()),
        }
    }

    pub fn is_empty(&self) -> bool {
        let guard = self.cache.lock().unwrap();
        (&*guard).is_empty()
    }

    pub fn len(&self) -> usize {
        let guard = self.cache.lock().unwrap();
        (&*guard).values().count()
    }

    pub fn get(&self, key: &Key) -> Option<Result<Vec<Range<MetaData>>, String>> {
        let guard = match self.cache.lock() {
            Ok(x) => x,
            Err(_) => panic!("Could not lock mutex in meta cache"),
        };
        guard.get(key).map(|n| n.clone())
    }

    pub fn insert(&self, key: Key, data: Result<Vec<Range<MetaData>>, String>) {
        let mut guard = match self.cache.lock() {
            Ok(x) => x,
            Err(_) => panic!("Could not lock mutex in meta cache"),
        };
        guard.insert(key, data);
    }

    pub fn store(self, file: &str) -> Result<(), String> {
        use std::fs::File;
        use deflate::write::DeflateEncoder;
        use deflate::Compression;

        let store: MetaStore = self.into();
        let mut w = DeflateEncoder::new(File::create(file)
            .map_err(|_| format!("Could not write to `{}`", file))?, Compression::Default);
        bincode::serialize_into(&mut w, &store)
            .map_err(|_| format!("Serialization to file `{}` failed", file))
    }

    pub fn restore(file: &str) -> MetaCache {
        use std::fs::File;
        use inflate::DeflateDecoder;

        let file = match File::open(file) {
            Ok(x) => x,
            Err(_) => return MetaCache::new(),
        };
        let r = DeflateDecoder::new(file);
        let store: MetaStore = match bincode::deserialize_from(r) {
            Ok(x) => x,
            Err(_) => return MetaCache::new(),
        };
        store.into()
    }
}

#[derive(Serialize, Deserialize)]
pub struct MetaStore {
    pub strings: Vec<String>,
    pub data: Vec<((u32, u32), Result<Vec<(u32, u32, MetaDataStore)>, String>)>,
}

impl From<MetaStore> for MetaCache {
    fn from(store: MetaStore) -> MetaCache {
        let MetaStore {data, strings} = store;

        let mut map = HashMap::new();
        let strings: Vec<Arc<String>> = strings.into_iter().map(|n| Arc::new(n)).collect();
        for (key, val) in data.into_iter() {
            let val = match val {
                Ok(val) => Ok(val.into_iter().map(|n| Range::new(n.0 as usize, n.1 as usize)
                    .wrap(n.2.to(&strings))).collect()),
                Err(err) => Err(err)
            };
            map.insert(Key {source: strings[key.0 as usize].clone(),
                            syntax: strings[key.1 as usize].clone()}, val);
        }
        MetaCache {
            cache: Arc::new(map.into()),
        }
    }
}

impl From<MetaCache> for MetaStore {
    fn from(cache: MetaCache) -> MetaStore {
        let mut data = vec![];
        let cache = cache.cache.lock().unwrap();
        let mut strings = vec![];
        let mut strings_cache: HashMap<String, u32> = HashMap::new();
        for (key, val) in cache.iter() {
            let val = match val {
                Ok(val) => Ok(val.iter().map(|n| {
                    (n.offset as u32,
                     n.length as u32,
                     MetaDataStore::from(n.data.clone(), &mut strings, &mut strings_cache))
                }).collect()),
                Err(err) => Err(err.clone()),
            };
            let source = id(&**key.source, &mut strings, &mut strings_cache);
            let syntax = id(&**key.syntax, &mut strings, &mut strings_cache);
            data.push(((source, syntax), val));
        }
        MetaStore {
            strings,
            data,
        }
    }
}

fn id(s: &str, strings: &mut Vec<String>, strings_cache: &mut HashMap<String, u32>) -> u32 {
    if let Some(id) = strings_cache.get(s) {
        *id
    } else {
        let id = strings.len();
        strings.push(s.into());
        strings_cache.insert(s.into(), id as u32);
        id as u32
    }
}

#[derive(Serialize, Deserialize)]
pub enum MetaDataStore {
    StartNode(u32),
    EndNode(u32),
    Bool(u32, bool),
    F64(u32, f64),
    String(u32, u32),
}

impl MetaDataStore {
    pub fn to(self, strings: &[Arc<String>]) -> MetaData {
        match self {
            MetaDataStore::StartNode(n) => MetaData::StartNode(strings[n as usize].clone()),
            MetaDataStore::EndNode(n) => MetaData::EndNode(strings[n as usize].clone()),
            MetaDataStore::Bool(n, v) => MetaData::Bool(strings[n as usize].clone(), v),
            MetaDataStore::F64(n, v) => MetaData::F64(strings[n as usize].clone(), v),
            MetaDataStore::String(n, v) => MetaData::String(strings[n as usize].clone(),
                                                            strings[v as usize].clone()),
        }
    }

    pub fn from(
        val: MetaData,
        strings: &mut Vec<String>,
        strings_cache: &mut HashMap<String, u32>
    ) -> MetaDataStore {
        match val {
            MetaData::StartNode(n) => MetaDataStore::StartNode(id(&**n, strings, strings_cache)),
            MetaData::EndNode(n) => MetaDataStore::EndNode(id(&**n, strings, strings_cache)),
            MetaData::Bool(n, v) => MetaDataStore::Bool(id(&**n, strings, strings_cache), v),
            MetaData::F64(n, v) => MetaDataStore::F64(id(&**n, strings, strings_cache), v),
            MetaData::String(n, v) => MetaDataStore::String(id(&**n, strings, strings_cache),
                                                            id(&**v, strings, strings_cache)),
        }
    }
}

