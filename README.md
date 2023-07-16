# ICTAC2023

ICTAC2023 Paper & Experiment

## Project Description

This project is developed to replicate the experimental process described in the ICTAC2023 paper. It utilizes the zaligvinder framework for automated benchmarking, data collection, and statistical analysis. For the complete version of the paper, please refer to ICTAC2023.pdf.

## System Requirements

- Linux system (e.g., Ubuntu 20.04)
- Python 3.x

## Installation Dependencies

Before running the project, make sure to install the required software packages. Follow the steps below to install the dependencies:

1. Open a terminal and navigate to the project root directory.
2. Run the following command to install the dependencies:

   ```shell
   pip install -r zaligvinder/requirements.txt
   ```

## Viewing Experimental Results

To view the experimental results mentioned in the paper, follow these steps:

1. Navigate to the `zaligvinder` folder in the project directory.
2. Run the `starwebserver.py` file to start a web server:
    - Open a terminal and navigate to the `zaligvinder` folder.
    - Run the following command:

      ```shell
      python3 starwebserver.py
      ```

    - Access `http://localhost:8081` in your browser to view the results.

## Replicating the Experiment

To replicate the experiment process and view the final statistical data, follow these steps:

1. Navigate to the `zaligvinder` folder in the project directory.
2. Run the `ICTAC2023.py` file to execute the experiment:
    - Open a terminal and navigate to the `zaligvinder` folder.
    - Run the following command:

      ```shell
      python3 ICTAC2023.py
      ```

    - Access `http://localhost:8081` in your browser to view the final statistical data.

