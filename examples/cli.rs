/// Reads numbers from stdin, one per line, and writes them to a serialized histogram on stdout.

extern crate hdrsample;
extern crate clap;

use std::io;
use std::io::{Write, BufRead};
use std::fmt::Display;

use clap::{App, Arg, SubCommand};

use hdrsample::{Histogram, RecordError};
use hdrsample::serialization::{V2Serializer, V2SerializeError, V2DeflateSerializer, V2DeflateSerializeError, Deserializer, DeserializeError};

fn main() {
    let default_max = format!("{}", u64::max_value());
    let matches = App::new("hdrsample cli")
            .subcommand(SubCommand::with_name("serialize")
                    .about("Transform number-per-line input from stdin into a serialized histogram on stdout")
                    .arg(Arg::with_name("min")
                            .long("min")
                            .help("Minimum discernible value")
                            .takes_value(true)
                            .default_value("1"))
                    .arg(Arg::with_name("max")
                            .long("max")
                            .help("Maximum trackable value")
                            .takes_value(true)
                            .default_value(default_max.as_str()))
                    .arg(Arg::with_name("sigfig")
                            .long("sigfig")
                            .help("Number of significant digits")
                            .takes_value(true)
                            .default_value("3"))
                    .arg(Arg::with_name("compression")
                            .short("c")
                            .long("compression")
                            .help("Enable compression"))
                    .arg(Arg::with_name("resize")
                            .short("r")
                            .long("resize")
                            .help("Enable auto resize")))
            .subcommand(SubCommand::with_name("iter-quantiles")
                    .about("Display quantiles to stdout from serialized histogram stdin")
                    .arg(Arg::with_name("ticks")
                            .short("t")
                            .long("ticks-per-half")
                            .takes_value(true)
                            .required(true)
                            .help("Ticks per half distance"))
                    .arg(Arg::with_name("quantile-precision")
                            .long("quantile-precision")
                            .takes_value(true)
                            .default_value("20")))
            .get_matches();

    let stdin = std::io::stdin();
    let stdin = stdin.lock();

    let stdout = std::io::stdout();
    let stdout = stdout.lock();

    match matches.subcommand_name() {
        Some("serialize") => {
            let sub_matches = matches.subcommand_matches("serialize").unwrap();
            let min = sub_matches.value_of("min").unwrap().parse().unwrap();
            let max = sub_matches.value_of("max").unwrap().parse().unwrap();
            let sigfig = sub_matches.value_of("sigfig").unwrap().parse().unwrap();

            let mut h: Histogram<u64> = Histogram::new_with_bounds(min, max, sigfig).unwrap();

            if sub_matches.is_present("resize") {
                h.auto(true);
            }

            serialize(stdin, stdout, h, sub_matches.is_present("compression"))
        }
        Some("iter-quantiles") => {
            let sub_matches = matches.subcommand_matches("iter-quantiles").unwrap();
            let ticks_per_half = sub_matches.value_of("ticks").unwrap().parse().unwrap();
            let quantile_precision = sub_matches.value_of("quantile-precision").unwrap().parse().unwrap();
            quantiles(stdin, stdout, quantile_precision, ticks_per_half)
        }
        _ => unreachable!()
    }.expect("Subcommand failed")
}

/// Read numbers, one from each line, from stdin and output the resulting serialized histogram.
fn serialize<R: BufRead, W: Write>(reader: R, mut writer: W, mut h: Histogram<u64>, compression: bool) -> Result<(), CliError> {
    for num in reader.lines()
            .map(|l| l.expect("Should be able to read stdin"))
            .map(|s| s.parse().expect("Each line must be a u64")) {
        h.record(num)?;
    }

    if compression {
        V2DeflateSerializer::new().serialize(&h, &mut writer)?;
    } else {
        V2Serializer::new().serialize(&h, &mut writer)?;
    }

    Ok(())
}

/// Output histogram data in a format similar to the Java impl's
/// `AbstractHistogram#outputPercentileDistribution`.
fn quantiles<R: BufRead, W: Write>(mut reader: R, mut writer: W, quantile_precision: usize, ticks_per_half: u32) -> Result<(), CliError> {
    let hist: Histogram<u64> = Deserializer::new().deserialize(&mut reader)?;

    writer.write_all(
        format!(
            "{:>12} {:>quantile_precision$} {:>quantile_precision$} {:>10} {:>14}\n\n",
            "Value",
            "QuantileValue",
            "QuantileIteration",
            "TotalCount",
            "1/(1-Quantile)",
            quantile_precision = quantile_precision + 2 // + 2 from leading "0." for numbers
        ).as_ref(),
    )?;
    let mut sum = 0;
    for v in hist.iter_quantiles(ticks_per_half) {
        sum += v.count_since_last_iteration();
        if v.quantile() < 1.0 {
            writer.write_all(
                format!(
                    "{:12} {:1.*} {:1.*} {:10} {:14.2}\n",
                    v.value(),
                    quantile_precision,
                    v.quantile(),
                    quantile_precision,
                    v.quantile_iterated_to(),
                    sum,
                    1_f64 / (1_f64 - v.quantile())
                ).as_ref(),
            )?;
        } else {
            writer.write_all(
                format!(
                    "{:12} {:1.*} {:1.*} {:10} {:>14}\n",
                    v.value(),
                    quantile_precision,
                    v.quantile(),
                    quantile_precision,
                    v.quantile_iterated_to(),
                    sum,
                    "∞"
                ).as_ref(),
            )?;
        }
    }

    fn write_extra_data<T1: Display, T2: Display, W: Write>(
        writer: &mut W, label1: &str, data1: T1, label2: &str, data2: T2) -> Result<(), io::Error> {
        writer.write_all(format!("#[{:10} = {:12.2}, {:14} = {:12.2}]\n",
                                 label1, data1, label2, data2).as_ref())
    }

    write_extra_data(&mut writer, "Mean", hist.mean(), "StdDeviation", hist.stdev())?;
    write_extra_data(&mut writer, "Max", hist.max(), "Total count", hist.count())?;
    write_extra_data(&mut writer, "Buckets", hist.buckets(), "SubBuckets", hist.len())?;

    Ok(())
}


// A handy way to enable ? use in subcommands by mapping common errors.
// Normally I frown on excessive use of From as it's too "magic", but in the limited confines of
// subcommands, the convenience seems worth it.
#[derive(Debug)]
enum CliError {
    IoError(io::Error),
    HistogramSerializeError(V2SerializeError),
    HistogramSerializeCompressedError(V2DeflateSerializeError),
    HistogramDeserializeError(DeserializeError),
    HistogramRecordError(RecordError)
}

impl From<io::Error> for CliError {
    fn from(e: io::Error) -> Self {
        CliError::IoError(e)
    }
}

impl From<V2SerializeError> for CliError {
    fn from(e: V2SerializeError) -> Self {
        CliError::HistogramSerializeError(e)
    }
}

impl From<V2DeflateSerializeError> for CliError {
    fn from(e: V2DeflateSerializeError) -> Self {
        CliError::HistogramSerializeCompressedError(e)
    }
}

impl From<RecordError> for CliError {
    fn from(e: RecordError) -> Self {
        CliError::HistogramRecordError(e)
    }
}

impl From<DeserializeError> for CliError {
    fn from(e: DeserializeError) -> Self {
        CliError::HistogramDeserializeError(e)
    }
}
