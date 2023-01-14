use mxrxtx::download;
use mxrxtx::offer;
use mxrxtx::protocol;
use mxrxtx::signaling::SignalingRouter;
use mxrxtx::test_signaling::TestSignalingRouter;
use mxrxtx::transport::Transport;
use std::sync::Arc;
use std::{
    fs::{self, File},
    io::Write,
    path::Path,
};
use tempdir::TempDir;
use tokio::sync::Mutex;

fn compare_directories(path1: &Path, path2: &Path) -> Result<(), ()> {
    // Get the list of entries in the first directory
    let entries1 = fs::read_dir(path1).expect("Error reading directory 1");
    let mut differs = false;

    // Iterate over the entries in the first directory
    for entry1 in entries1 {
        let entry1 = entry1.expect("Error reading entry from directory 1");
        let file_name = entry1.file_name();

        let path1 = entry1.path();
        let path2 = path2.join(file_name.clone());
        let file1_contents = fs::read_to_string(path1.clone()).expect(&format!(
            "Error reading file from directory 1: {}",
            path1.to_string_lossy()
        ));
        let file2_contents = fs::read_to_string(path2.clone()).expect(&format!(
            "Error reading file from directory 2: {}",
            path2.to_string_lossy()
        ));
        if file1_contents != file2_contents {
            println!("The file {} differs", file_name.to_string_lossy());
            differs = true;
        }
    }
    if differs {
        Err(())
    } else {
        Ok(())
    }
}

#[tokio::test]
async fn transfer_file() {
    println!("start");
    let mut offer_content = protocol::OfferContent::default();
    offer_content.files.push(protocol::File {
        name: String::from("test-file.1"),
        content_type: String::from("application/octet-stream"),
        size: 10,
    });
    let offer_tmp_dir = Arc::new(Mutex::new(Some(
        TempDir::new("mxrxtx-transfer_tests-offer").unwrap(),
    )));
    let download_tmp_dir = Arc::new(Mutex::new(Some(
        TempDir::new("mxrxtx-transfer_tests-download").unwrap(),
    )));
    let signaling = TestSignalingRouter::new();
    let offer_task = tokio::spawn({
        let offer_content = offer_content.clone();
        let offer_tmp_dir = offer_tmp_dir.clone();
        let mut signaling = signaling.clone();
        async move {
            let mut transport =
                Transport::new(signaling.accept().await.unwrap(), vec![]).expect("weird");
            let mut files = Vec::new();
            for file in &offer_content.files {
                let offer_tmp_dir = offer_tmp_dir.lock().await;
                let file_path = offer_tmp_dir
                    .as_ref()
                    .unwrap()
                    .path()
                    .join(file.name.clone());
                let mut tmp_file = File::create(file_path.clone()).unwrap();
                for _ in 0..file.size {
                    tmp_file.write(b"b").unwrap();
                }
                files.push(file_path.to_path_buf());
            }
            offer::transfer(files, transport.accept().await.unwrap())
                .await
                .map_err(anyhow::Error::from)
        }
    });
    let download_task = tokio::spawn({
        let download_tmp_dir = download_tmp_dir.clone();
        let mut signaling = signaling.clone();
        async move {
            let transport = Transport::new(signaling.connect().await, vec![]).expect("weird");
            let download_path = {
                let download_tmp_dir = download_tmp_dir.lock().await;
                String::from(download_tmp_dir.as_ref().unwrap().path().to_str().unwrap())
            };
            download::transfer(download_path, transport, offer_content)
                .await
                .map_err(anyhow::Error::from)
        }
    });
    let mut handles = vec![];
    handles.push(offer_task);
    handles.push(download_task);
    for retval in futures::future::join_all(handles).await {
        match retval.unwrap() {
            Ok(()) => (),
            Err(err) => {
                panic!("task failed: {:?}", err)
            }
        }
    }
    {
        let offer_tmp_dir = offer_tmp_dir.lock().await;
        let download_tmp_dir = download_tmp_dir.lock().await;
        compare_directories(
            offer_tmp_dir.as_ref().unwrap().path(),
            download_tmp_dir.as_ref().unwrap().path(),
        )
        .unwrap();
    }
    println!("exit");
    offer_tmp_dir.lock().await.take().unwrap().close().unwrap();
    download_tmp_dir
        .lock()
        .await
        .take()
        .unwrap()
        .close()
        .unwrap();
}
